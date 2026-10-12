import QLean.Generator.Implementation.BitonicTotalStageCompiler
import QLean.Generator.Implementation.QBitonicCircuitCorrectness
import QLean.Generator.Implementation.QOracleEventComputedClean
import QLean.Circuits.Foundation.BitonicClean
import QLean.Circuits.Foundation.EqualityBranchLessThanAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.Combinators

/-!
# Shared clean bitonic contract at the Q layout

This module instantiates the shared clean compare--swap plan.  Only the Q wire
layout, the frozen equality-branch compiler transport, and the Q readout
predicates live here.
-/

namespace ProbabilityGeneratorQProof

noncomputable section

namespace BitonicSharedClean

open VerifiedCircuitCore

/-- The Q comparison-work list viewed as a fixed-width validated register. -/
def compareValidatedRegister (p : QParameters) :
    ValidatedQRegister p.ancillaWidth p.systemWidth (p.wordWidth + 1) :=
  ValidatedQRegister.ofListWithLength (sortCompareWorkWires p)
    (ReversibleCircuit.sortCompareWorkWires_nodup p)
      (ReversibleCircuit.sortCompareWorkWires_length p)

@[simp] theorem candidateValidatedRegister_wires (p : QParameters)
    (word : Fin p.sortWordCount) :
    (BitonicTotalProgram.candidateValidatedRegister p word).wires =
      candidateWordAt p word := by
  simp [BitonicTotalProgram.candidateValidatedRegister,
    ValidatedQRegister.wires, candidateWordAt]

/-- The canonical core history wire used by one typed instruction. -/
def historyCoreWire (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    Fin (p.ancillaWidth + p.systemWidth) :=
  analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history)

private theorem candidateWire_mem (p : QParameters)
    (word : Fin p.sortWordCount) (index : Fin (p.wordWidth + 1)) :
    (BitonicTotalProgram.candidateValidatedRegister p word).wire index ∈
      candidateWordAt p word := by
  simp [BitonicTotalProgram.candidateValidatedRegister, candidateWordAt,
    candidateWordWire]

private theorem compareWire_mem (p : QParameters)
    (index : Fin (p.wordWidth + 1)) :
    (compareValidatedRegister p).wire index ∈ sortCompareWorkWires p := by
  have wires := ValidatedQRegister.wires_ofListWithLength
    (sortCompareWorkWires p) (ReversibleCircuit.sortCompareWorkWires_nodup p)
      (ReversibleCircuit.sortCompareWorkWires_length p)
  have member :
      (compareValidatedRegister p).wire index ∈
        (compareValidatedRegister p).wires := by
    simp [ValidatedQRegister.wires]
  simpa [compareValidatedRegister] using member

private theorem coreWire_ne_of_ne {p : QParameters}
    {left right : Wire p.ancillaWidth p.systemWidth} (different : left ≠ right) :
    analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth left ≠
      analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth right :=
  (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective.ne different

/-- One Q typed instruction as a shared physical compare--swap specification. -/
def compareSwapSpec (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    ControlledWordCompareSwapSpec (p.ancillaWidth + p.systemWidth)
      (p.wordWidth + 1) := by
  let left := BitonicTotalProgram.candidateValidatedRegister p instruction.left
  let right := BitonicTotalProgram.candidateValidatedRegister p instruction.right
  let borrow := compareValidatedRegister p
  let history := historyCoreWire p instruction
  have different := ReversibleCircuit.qTypedBitonicSchedule_left_ne_right
    p instruction member
  let swapLayout := BitonicTotalProgram.controlledSwapValidatedLayout p instruction different
  let lhs := if instruction.ascending then right else left
  let rhs := if instruction.ascending then left else right
  refine
    { ascending := instruction.ascending
      compare :=
        { widthPositive := by omega
          lhs := lhs.toCore
          rhs := rhs.toCore
          borrow := borrow.toCore
          target := history
          lhsRhsDifferent := ?_
          lhsBorrowDifferent := ?_
          rhsBorrowDifferent := ?_
          targetLhsDifferent := ?_
          targetRhsDifferent := ?_
          targetBorrowDifferent := ?_ }
      swap := swapLayout.toCore
      compareTarget_eq_swapControl := rfl
      compareOperands_eq_swapOperands := ?_ }
  · intro lhsIndex rhsIndex equal
    cases ascendingValue : instruction.ascending <;>
      simp only [lhs, rhs, ascendingValue, if_true] at equal
    · have qEqual := (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
      have qEqual' :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire lhsIndex =
            (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire rhsIndex := by
        simpa [lhs, rhs, left, right, ascendingValue] using qEqual
      have leftMember := candidateWire_mem p instruction.left lhsIndex
      have rightMember := candidateWire_mem p instruction.right rhsIndex
      have rightMemberAtLeft :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire lhsIndex ∈
            candidateWordAt p instruction.right := by
        rw [qEqual']
        exact rightMember
      exact (List.disjoint_left.mp
        (ReversibleCircuit.sortCandidateWordAt_disjoint_of_ne
          p instruction.left instruction.right different)
          leftMember) rightMemberAtLeft
    · have qEqual := (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
      have qEqual' :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire lhsIndex =
            (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire rhsIndex := by
        simpa [lhs, rhs, left, right, ascendingValue] using qEqual
      have rightMember := candidateWire_mem p instruction.right lhsIndex
      have leftMember := candidateWire_mem p instruction.left rhsIndex
      have leftMemberAtRight :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire lhsIndex ∈
            candidateWordAt p instruction.left := by
        rw [qEqual']
        exact leftMember
      exact (List.disjoint_left.mp
        (ReversibleCircuit.sortCandidateWordAt_disjoint_of_ne
          p instruction.left instruction.right different).symm
          rightMember) leftMemberAtRight
  · intro lhsIndex borrowIndex equal
    have qEqual := (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
    cases ascendingValue : instruction.ascending <;>
      simp only [lhs, ascendingValue, if_true] at qEqual
    · have compareMemberAtCandidate :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire lhsIndex ∈
            sortCompareWorkWires p := by
          rw [show
              (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire lhsIndex =
                (compareValidatedRegister p).wire borrowIndex by
            simpa [lhs, left, right, borrow, ascendingValue] using qEqual]
          exact compareWire_mem p borrowIndex
      exact (List.disjoint_left.mp
        (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p instruction.left)
          (candidateWire_mem p instruction.left lhsIndex))
            compareMemberAtCandidate
    · have compareMemberAtCandidate :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire lhsIndex ∈
            sortCompareWorkWires p := by
          rw [show
              (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire lhsIndex =
                (compareValidatedRegister p).wire borrowIndex by
            simpa [lhs, left, right, borrow, ascendingValue] using qEqual]
          exact compareWire_mem p borrowIndex
      exact (List.disjoint_left.mp
        (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p instruction.right)
          (candidateWire_mem p instruction.right lhsIndex))
            compareMemberAtCandidate
  · intro rhsIndex borrowIndex equal
    have qEqual := (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
    cases ascendingValue : instruction.ascending <;>
      simp only [rhs, ascendingValue, if_true] at qEqual
    · have compareMemberAtCandidate :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire rhsIndex ∈
            sortCompareWorkWires p := by
          rw [show
              (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire rhsIndex =
                (compareValidatedRegister p).wire borrowIndex by
            simpa [rhs, left, right, borrow, ascendingValue] using qEqual]
          exact compareWire_mem p borrowIndex
      exact (List.disjoint_left.mp
        (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p instruction.right)
          (candidateWire_mem p instruction.right rhsIndex))
            compareMemberAtCandidate
    · have compareMemberAtCandidate :
          (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire rhsIndex ∈
            sortCompareWorkWires p := by
          rw [show
              (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire rhsIndex =
                (compareValidatedRegister p).wire borrowIndex by
            simpa [rhs, left, right, borrow, ascendingValue] using qEqual]
          exact compareWire_mem p borrowIndex
      exact (List.disjoint_left.mp
        (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p instruction.left)
          (candidateWire_mem p instruction.left rhsIndex))
            compareMemberAtCandidate
  · intro index equal
    have qEqual :=
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
    cases ascendingValue : instruction.ascending with
    | false =>
        apply ReversibleCircuit.sortHistoryWire_not_mem_candidate
          p instruction.history instruction.left
        rw [show (QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history =
            (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire index by
          simpa [lhs, history, historyCoreWire, ascendingValue] using qEqual]
        exact candidateWire_mem p instruction.left index
    | true =>
        apply ReversibleCircuit.sortHistoryWire_not_mem_candidate
          p instruction.history instruction.right
        rw [show (QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history =
            (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire index by
          simpa [lhs, history, historyCoreWire, ascendingValue] using qEqual]
        exact candidateWire_mem p instruction.right index
  · intro index equal
    have qEqual :=
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
    cases ascendingValue : instruction.ascending with
    | false =>
        apply ReversibleCircuit.sortHistoryWire_not_mem_candidate
          p instruction.history instruction.right
        rw [show (QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history =
            (BitonicTotalProgram.candidateValidatedRegister p instruction.right).wire index by
          simpa [rhs, history, historyCoreWire, ascendingValue] using qEqual]
        exact candidateWire_mem p instruction.right index
    | true =>
        apply ReversibleCircuit.sortHistoryWire_not_mem_candidate
          p instruction.history instruction.left
        rw [show (QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history =
            (BitonicTotalProgram.candidateValidatedRegister p instruction.left).wire index by
          simpa [rhs, history, historyCoreWire, ascendingValue] using qEqual]
        exact candidateWire_mem p instruction.left index
  · intro index equal
    apply ReversibleCircuit.sortHistoryWire_not_mem_compare p instruction.history
    have qEqual := (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
    rw [show (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history =
        (compareValidatedRegister p).wire index by
      simpa [history, historyCoreWire, borrow] using qEqual]
    exact compareWire_mem p index
  · by_cases ascending : instruction.ascending = true
    · dsimp only [lhs, rhs, swapLayout,
        BitonicTotalProgram.controlledSwapValidatedLayout,
        ValidatedControlledRegisterSwapLayout.toCore]
      simp only [ascending, if_true]
      dsimp only [left, right]
      constructor <;> rfl
    · dsimp only [lhs, rhs, swapLayout,
        BitonicTotalProgram.controlledSwapValidatedLayout,
        ValidatedControlledRegisterSwapLayout.toCore]
      have descending : instruction.ascending = false :=
        Bool.eq_false_of_not_eq_true ascending
      simp only [descending, Bool.false_eq_true, if_false]
      dsimp only [left, right]
      constructor <;> rfl

/-- Shared physical specifications in frozen execution order. -/
def compareSwapSpecs (p : QParameters) :
    List (ControlledWordCompareSwapSpec (p.ancillaWidth + p.systemWidth)
      (p.wordWidth + 1)) :=
  (qTypedBitonicSchedule p).attach.map fun entry =>
    compareSwapSpec p entry.1 entry.2

/-- Frozen comparison lhs, including the ascending operand reversal. -/
def comparisonLeftWires (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  if instruction.ascending then candidateWordAt p instruction.right
  else candidateWordAt p instruction.left

/-- Frozen comparison rhs, including the ascending operand reversal. -/
def comparisonRightWires (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  if instruction.ascending then candidateWordAt p instruction.left
  else candidateWordAt p instruction.right

/-- Validated left comparison operand in the frozen ascending convention. -/
def comparisonLeftRegister (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    ValidatedQRegister p.ancillaWidth p.systemWidth (p.wordWidth + 1) :=
  if instruction.ascending then
    BitonicTotalProgram.candidateValidatedRegister p instruction.right
  else BitonicTotalProgram.candidateValidatedRegister p instruction.left

/-- Validated right comparison operand in the frozen ascending convention. -/
def comparisonRightRegister (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    ValidatedQRegister p.ancillaWidth p.systemWidth (p.wordWidth + 1) :=
  if instruction.ascending then
    BitonicTotalProgram.candidateValidatedRegister p instruction.left
  else BitonicTotalProgram.candidateValidatedRegister p instruction.right

@[simp] theorem comparisonLeftRegister_wires (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    (comparisonLeftRegister p instruction).wires =
      comparisonLeftWires p instruction := by
  cases ascending : instruction.ascending <;>
    simp [comparisonLeftRegister, comparisonLeftWires, ascending,
      ValidatedQRegister.wires, BitonicTotalProgram.candidateValidatedRegister,
      candidateWordAt]

@[simp] theorem comparisonRightRegister_wires (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    (comparisonRightRegister p instruction).wires =
      comparisonRightWires p instruction := by
  cases ascending : instruction.ascending <;>
    simp [comparisonRightRegister, comparisonRightWires, ascending,
      ValidatedQRegister.wires, BitonicTotalProgram.candidateValidatedRegister,
      candidateWordAt]

/-- The exact Q layout required by the shared equality-branch comparator. -/
theorem comparisonFullLayout (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (comparisonLeftWires p instruction ++ comparisonRightWires p instruction ++
      sortCompareWorkWires p ++ sortAndScratchWires p ++
      [(QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history]).Nodup := by
  have original := ReversibleCircuit.qTypedBitonicInstruction_layout
    p instruction member
  by_cases ascending : instruction.ascending = true
  · have normalized :
        (candidateWordAt p instruction.left ++
          candidateWordAt p instruction.right ++
          (sortCompareWorkWires p ++ sortAndScratchWires p ++
            [(QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire
                instruction.history])).Nodup := by
      simpa [List.append_assoc] using original
    have swapped :
        (candidateWordAt p instruction.right ++
          candidateWordAt p instruction.left).Perm
        (candidateWordAt p instruction.left ++
          candidateWordAt p instruction.right) := List.perm_append_comm
    have permutation := swapped.append_right
      (sortCompareWorkWires p ++ sortAndScratchWires p ++
        [(QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history])
    have reversed := permutation.nodup_iff.mpr normalized
    simpa [comparisonLeftWires, comparisonRightWires, ascending,
      List.append_assoc] using reversed
  · have descending : instruction.ascending = false :=
      Bool.eq_false_of_not_eq_true ascending
    simpa [comparisonLeftWires, comparisonRightWires, descending] using original

/-- Reindexing the Q comparison layout preserves duplicate-freedom. -/
theorem comparisonCanonicalCoreFullLayout (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (analyticWiresToCore (comparisonLeftWires p instruction) ++
      analyticWiresToCore (comparisonRightWires p instruction) ++
      analyticWiresToCore (sortCompareWorkWires p) ++
      analyticWiresToCore (sortAndScratchWires p) ++
      [historyCoreWire p instruction]).Nodup := by
  have layout := comparisonFullLayout p instruction member
  have mapped := layout.map
    (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective
  simpa [analyticWiresToCore, historyCoreWire, List.map_append] using mapped

/-- The frozen equality-branch comparator as a shared validated clean plan. -/
def equalityBranchSpec (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    ClassicalReversibleStage.EqualityBranchUnsignedLessThanSpec
      (p.ancillaWidth + p.systemWidth) :=
  ClassicalReversibleStage.EqualityBranchUnsignedLessThanSpec.ofFullLayout
    (analyticWiresToCore (comparisonLeftWires p instruction))
    (analyticWiresToCore (comparisonRightWires p instruction))
    (analyticWiresToCore (sortCompareWorkWires p))
    (analyticWiresToCore (sortAndScratchWires p))
    (historyCoreWire p instruction)
    (by
      by_cases ascending : instruction.ascending = true
      · simp [analyticWiresToCore, comparisonLeftWires, candidateWordAt,
          sortCompareWorkWires, ascending]
      · have descending : instruction.ascending = false :=
          Bool.eq_false_of_not_eq_true ascending
        simp [analyticWiresToCore, comparisonLeftWires, candidateWordAt,
          sortCompareWorkWires, descending])
    (by
      by_cases ascending : instruction.ascending = true
      · simp [analyticWiresToCore, comparisonRightWires, candidateWordAt,
          sortCompareWorkWires, ascending]
      · have descending : instruction.ascending = false :=
          Bool.eq_false_of_not_eq_true ascending
        simp [analyticWiresToCore, comparisonRightWires, candidateWordAt,
          sortCompareWorkWires, descending])
    (comparisonCanonicalCoreFullLayout p instruction member)
    (by
      simpa [analyticWiresToCore] using
        ReversibleCircuit.sortCompareWorkWires_length_le_scratch p)

@[simp] theorem equalityBranchSpec_left (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (equalityBranchSpec p instruction member).left =
      analyticWiresToCore (comparisonLeftRegister p instruction).wires := by
  change analyticWiresToCore (comparisonLeftWires p instruction) = _
  rw [comparisonLeftRegister_wires]

@[simp] theorem equalityBranchSpec_right (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (equalityBranchSpec p instruction member).right =
      analyticWiresToCore (comparisonRightRegister p instruction).wires := by
  change analyticWiresToCore (comparisonRightWires p instruction) = _
  rw [comparisonRightRegister_wires]

@[simp] theorem equalityBranchSpec_equalFlags (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (equalityBranchSpec p instruction member).equalFlags =
      analyticWiresToCore (sortCompareWorkWires p) := by
  rfl

@[simp] theorem equalityBranchSpec_scratch (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (equalityBranchSpec p instruction member).scratch =
      analyticWiresToCore (sortAndScratchWires p) := by
  rfl

@[simp] theorem compareSwapSpec_compare_lhs (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (compareSwapSpec p instruction member).compare.lhs =
      (comparisonLeftRegister p instruction).toCore := by
  by_cases ascending : instruction.ascending = true
  · simp [compareSwapSpec, comparisonLeftRegister, ascending]
  · have descending : instruction.ascending = false :=
      Bool.eq_false_of_not_eq_true ascending
    simp [compareSwapSpec, comparisonLeftRegister, descending]

@[simp] theorem compareSwapSpec_compare_rhs (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (compareSwapSpec p instruction member).compare.rhs =
      (comparisonRightRegister p instruction).toCore := by
  by_cases ascending : instruction.ascending = true
  · simp [compareSwapSpec, comparisonRightRegister, ascending]
  · have descending : instruction.ascending = false :=
      Bool.eq_false_of_not_eq_true ascending
    simp [compareSwapSpec, comparisonRightRegister, descending]

@[simp] theorem compareSwapSpec_compare_borrow (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (compareSwapSpec p instruction member).compare.borrow =
      (compareValidatedRegister p).toCore := by
  rfl

@[simp] theorem compareSwapSpec_compare_target (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (compareSwapSpec p instruction member).compare.target =
      historyCoreWire p instruction := by
  rfl

@[simp] theorem compareSwapSpec_swap (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (compareSwapSpec p instruction member).swap =
      (BitonicTotalProgram.controlledSwapValidatedLayout p instruction
        (ReversibleCircuit.qTypedBitonicSchedule_left_ne_right
          p instruction member)).toCore := by
  rfl

private theorem littleEndianListNat_validatedRegister
    {ancillaQubits systemQubits width : Nat}
    (register : ValidatedQRegister ancillaQubits systemQubits width)
    (input : QubitBasis (ancillaQubits + systemQubits)) :
    ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (analyticWiresToCore register.wires) input) =
      qubitBasisLittleEndianIndex width (register.toCore.read input) := by
  rw [show ClassicalReversibleStage.readWires
        (analyticWiresToCore register.wires) input =
      (List.finRange width).map
        (fun index => input
          (analyticCanonicalWireEquiv ancillaQubits systemQubits
            (register.wire index))) by
    simp [ClassicalReversibleStage.readWires, analyticWiresToCore,
      ValidatedQRegister.wires, List.map_map, Function.comp_def]]
  have readEq : register.toCore.read input =
      fun index => input
        (analyticCanonicalWireEquiv ancillaQubits systemQubits
          (register.wire index)) := by
    funext index
    rfl
  have decoded := ClassicalReversibleStage.littleEndianListNat_finRange
    (register.toCore.read input)
  rw [readEq] at decoded ⊢
  exact decoded

private theorem littleEndianListNat_eq_qLittleEndianNat
    (bits : List Bool) :
    ClassicalReversibleStage.littleEndianListNat bits =
      ReversibleCircuit.littleEndianNat bits := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp [ClassicalReversibleStage.littleEndianListNat,
        ReversibleCircuit.littleEndianNat, inductionHypothesis]

private theorem qubitBasisLittleEndianIndex_validatedRegister_toJoint
    {ancillaQubits systemQubits width : Nat}
    (register : ValidatedQRegister ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    qubitBasisLittleEndianIndex width
        (register.toCore.read
          (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)) =
      ReversibleCircuit.littleEndianNat
        (ReversibleCircuit.readWires register.wires input) := by
  have decoded := littleEndianListNat_validatedRegister register
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
  rw [← decoded, littleEndianListNat_eq_qLittleEndianNat]
  congr 1
  simp [ClassicalReversibleStage.readWires, ReversibleCircuit.readWires,
    analyticWiresToCore, ValidatedQRegister.wires, List.map_map,
    Function.comp_def, analyticJointBasisCoreEquiv,
    analyticCanonicalWireEquiv]

/-- The equality-branch and ripple-borrow specifications have the same direct
clean comparison action at the validated Q layout. -/
theorem equalityBranchSpec_basisAction_eq_cleanCompare (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth)) :
    (equalityBranchSpec p instruction member).basisAction input =
      unsignedLessThanXorCleanBasisAction
        (compareSwapSpec p instruction member).compare input := by
  unfold ClassicalReversibleStage.EqualityBranchUnsignedLessThanSpec.basisAction
    unsignedLessThanXorCleanBasisAction
  rw [unsignedLessThanBits_eq_decide_lt]
  simp only [equalityBranchSpec_left, equalityBranchSpec_right,
    compareSwapSpec_compare_lhs, compareSwapSpec_compare_rhs]
  rw [littleEndianListNat_validatedRegister
      (comparisonLeftRegister p instruction) input,
    littleEndianListNat_validatedRegister
      (comparisonRightRegister p instruction) input]
  rfl

private theorem compareCleanInput_of_equalityBranchClean (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : (equalityBranchSpec p instruction member).cleanInput input) :
    (compareSwapSpec p instruction member).compare.cleanInput input := by
  intro index
  apply clean.1
  rw [equalityBranchSpec_equalFlags, compareSwapSpec_compare_borrow]
  simpa [analyticWiresToCore, ValidatedQRegister.toCore] using
    (compareWire_mem p index)

private theorem toCore_reverse
    {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    stage.reverse.toCore = stage.toCore.reverse := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstHypothesis secondHypothesis =>
      simp [TotalReversibleStage.reverse, TotalReversibleStage.toCore,
        ClassicalReversibleStage.reverse, firstHypothesis, secondHypothesis]
  | «repeat» count body inductionHypothesis =>
      simp [TotalReversibleStage.reverse, TotalReversibleStage.toCore,
        ClassicalReversibleStage.reverse, inductionHypothesis]

private theorem lessThanControlProgram_toCore
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits)) :
    (TotalReversibleStage.lessThanControlProgram left right equalFlags).map
        analyticControlsToCore =
      ClassicalReversibleStage.equalityBranchLessThanControlProgram
        (analyticWiresToCore left) (analyticWiresToCore right)
        (analyticWiresToCore equalFlags) := by
  induction left generalizing right equalFlags with
  | nil => cases right <;> rfl
  | cons leftBit leftTail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons rightBit rightTail =>
          simp [TotalReversibleStage.lessThanControlProgram,
            ClassicalReversibleStage.equalityBranchLessThanControlProgram,
            analyticControlsToCore, analyticWiresToCore, List.map_map,
            Function.comp_def, inductionHypothesis]

private theorem toCore_boolLessThanProgram
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (TotalReversibleStage.sequence
        ((TotalReversibleStage.lessThanControlProgram left right equalFlags).map
          fun controls => TotalReversibleStage.boolMultiControlledX
            controls scratch target)).toCore =
      ClassicalReversibleStage.boolControlledXProgram
        (ClassicalReversibleStage.equalityBranchLessThanControlProgram
          (analyticWiresToCore left) (analyticWiresToCore right)
          (analyticWiresToCore equalFlags))
        (analyticWiresToCore scratch)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target) := by
  rw [TotalReversibleStage.toCore_sequence]
  unfold ClassicalReversibleStage.boolControlledXProgram
  rw [← lessThanControlProgram_toCore left right equalFlags]
  simp [List.map_map, Function.comp_def,
    TotalReversibleStage.boolMultiControlledX]

private theorem toCore_computeEqualityFlags
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits)) :
    (TotalReversibleStage.computeEqualityFlags left right equalFlags).toCore =
      ClassicalReversibleStage.computeEqualityFlags
        (analyticWiresToCore left) (analyticWiresToCore right)
        (analyticWiresToCore equalFlags) := by
  simp [TotalReversibleStage.computeEqualityFlags]

private theorem oracleCandidateWordAt_eq (p : QParameters)
    (word : Fin p.sortWordCount) :
    OracleEventTotalProgram.candidateWordAt p word = candidateWordAt p word := by
  rfl

private theorem compareWorkWires_eq (p : QParameters) :
    BitonicTotalProgram.compareWorkWires p = sortCompareWorkWires p := by
  rfl

private theorem andScratchWires_eq (p : QParameters) :
    BitonicTotalProgram.andScratchWires p = sortAndScratchWires p := by
  rfl

/-- The frozen Q comparison stage is the shared equality-branch stage after
canonical wire reindexing. -/
theorem comparisonStage_toCore_eq_equalityBranchStage (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (BitonicTotalProgram.comparisonStage p instruction).toCore =
      (equalityBranchSpec p instruction member).stage := by
  change (BitonicTotalProgram.comparisonStage p instruction).toCore =
    ClassicalReversibleStage.equalityBranchUnsignedLessThanStage
      (analyticWiresToCore (comparisonLeftWires p instruction))
      (analyticWiresToCore (comparisonRightWires p instruction))
      (analyticWiresToCore (sortCompareWorkWires p))
      (analyticWiresToCore (sortAndScratchWires p))
      (historyCoreWire p instruction)
  by_cases ascending : instruction.ascending = true
  · simp only [BitonicTotalProgram.comparisonStage, ascending, if_true,
      comparisonLeftWires, comparisonRightWires, historyCoreWire]
    rw [oracleCandidateWordAt_eq, oracleCandidateWordAt_eq,
      compareWorkWires_eq, andScratchWires_eq]
    unfold TotalReversibleStage.xorLessThanIntoTarget
      ClassicalReversibleStage.equalityBranchUnsignedLessThanStage
      ClassicalReversibleStage.computeUseUncompute
    simp only [TotalReversibleStage.toCore]
    rw [toCore_computeEqualityFlags, toCore_boolLessThanProgram,
      toCore_reverse, toCore_computeEqualityFlags]
  · have descending : instruction.ascending = false :=
      Bool.eq_false_of_not_eq_true ascending
    simp only [BitonicTotalProgram.comparisonStage, descending,
      Bool.false_eq_true, if_false, comparisonLeftWires,
      comparisonRightWires, historyCoreWire]
    rw [oracleCandidateWordAt_eq, oracleCandidateWordAt_eq,
      compareWorkWires_eq, andScratchWires_eq]
    unfold TotalReversibleStage.xorLessThanIntoTarget
      ClassicalReversibleStage.equalityBranchUnsignedLessThanStage
      ClassicalReversibleStage.computeUseUncompute
    simp only [TotalReversibleStage.toCore]
    rw [toCore_computeEqualityFlags, toCore_boolLessThanProgram,
      toCore_reverse, toCore_computeEqualityFlags]

/-- On clean comparison work, the frozen equality-branch stage has exactly
the shared direct comparison action used by one compare--swap specification. -/
theorem comparisonStage_reference_eq_compareDirty (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : (equalityBranchSpec p instruction member).cleanInput input) :
    (BitonicTotalProgram.comparisonStage p instruction).toCore.reference input =
      unsignedLessThanXorDirtyBasisAction
        (compareSwapSpec p instruction member).compare input := by
  rw [comparisonStage_toCore_eq_equalityBranchStage p instruction member]
  rw [(equalityBranchSpec p instruction member).stage_reference_apply_of_cleanWork
    input clean]
  rw [equalityBranchSpec_basisAction_eq_cleanCompare p instruction member input]
  exact (unsignedLessThanXorDirtyBasisAction_eq_clean
    (compareSwapSpec p instruction member).compare input
    (compareCleanInput_of_equalityBranchClean p instruction member input clean)).symm

/-- The clean frozen comparison stage toggles exactly its typed history bit
according to the Q little-endian comparison predicate. -/
theorem comparisonStage_reference_toJoint (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : (equalityBranchSpec p instruction member).cleanInput
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)) :
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
        ((BitonicTotalProgram.comparisonStage p instruction).toCore.reference
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)) =
      if decide
          (ReversibleCircuit.littleEndianNat
              (ReversibleCircuit.readWires
                (comparisonLeftWires p instruction) input) <
            ReversibleCircuit.littleEndianNat
              (ReversibleCircuit.readWires
                (comparisonRightWires p instruction) input)) then
        xBasisAction
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history) input
      else input := by
  have coreEq := comparisonStage_reference_eq_compareDirty p instruction member
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) clean
  rw [unsignedLessThanXorDirtyBasisAction_eq_clean
    (compareSwapSpec p instruction member).compare
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)
    (compareCleanInput_of_equalityBranchClean p instruction member _ clean)] at coreEq
  unfold unsignedLessThanXorCleanBasisAction at coreEq
  rw [unsignedLessThanBits_eq_decide_lt] at coreEq
  simp only [compareSwapSpec_compare_lhs, compareSwapSpec_compare_rhs,
    compareSwapSpec_compare_target] at coreEq
  rw [qubitBasisLittleEndianIndex_validatedRegister_toJoint
      (comparisonLeftRegister p instruction) input,
    qubitBasisLittleEndianIndex_validatedRegister_toJoint
      (comparisonRightRegister p instruction) input] at coreEq
  simp only [comparisonLeftRegister_wires, comparisonRightRegister_wires] at coreEq
  have qEq := congrArg
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm coreEq
  by_cases shouldSwap :
      ReversibleCircuit.littleEndianNat
          (ReversibleCircuit.readWires
            (comparisonLeftWires p instruction) input) <
        ReversibleCircuit.littleEndianNat
          (ReversibleCircuit.readWires
            (comparisonRightWires p instruction) input)
  · have decision : decide
        (ReversibleCircuit.littleEndianNat
            (ReversibleCircuit.readWires
              (comparisonLeftWires p instruction) input) <
          ReversibleCircuit.littleEndianNat
            (ReversibleCircuit.readWires
              (comparisonRightWires p instruction) input)) = true := by
      exact decide_eq_true shouldSwap
    rw [decision] at qEq ⊢
    simp only [if_true]
    have xTransport := analyticJointBasisCoreEquiv_xBasisAction
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) input
    have xBack := congrArg
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
      xTransport
    exact qEq.trans (by
      simpa [historyCoreWire] using xBack.symm)
  · have decision : decide
        (ReversibleCircuit.littleEndianNat
            (ReversibleCircuit.readWires
              (comparisonLeftWires p instruction) input) <
          ReversibleCircuit.littleEndianNat
            (ReversibleCircuit.readWires
              (comparisonRightWires p instruction) input)) = false :=
      decide_eq_false shouldSwap
    rw [decision] at qEq ⊢
    simpa [VerifiedCircuitCore.xorWire] using qEq

private theorem controlledSwapWordCore_eq_controlledRegisterSwapStage
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    TotalReversibleStage.controlledSwapWordCore layout.control
        layout.left.wires layout.right.wires =
      ClassicalReversibleStage.controlledRegisterSwapStage layout.toCore := by
  rw [controlledSwapWordCore_eq_validatedIndexSequence]
  unfold ClassicalReversibleStage.controlledRegisterSwapStage
  congr 1
  apply List.map_congr_left
  intro index _
  have leftRight :
      analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.left.wire index) ≠
        analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.right.wire index) :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.ne
      (layout.leftRightDisjoint index index)
  have controlLeft :
      analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control ≠
        analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.left.wire index) :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.ne
      (layout.controlLeftDifferent index)
  have controlRight :
      analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control ≠
        analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.right.wire index) :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.ne
      (layout.controlRightDifferent index)
  unfold TotalReversibleStage.controlledSwapBitCore
    ClassicalReversibleStage.fredkinStage
  simp only [ClassicalReversibleStage.safeXorControlled,
    ClassicalReversibleStage.safeXorDoublyControlled,
    dif_pos leftRight, dif_pos controlRight, dif_pos controlLeft,
    dif_pos (Ne.symm leftRight)]
  simp [ValidatedControlledRegisterSwapLayout.toCore,
    ValidatedQRegister.toCore]

/-- The frozen Q controlled-swap child has the shared full-basis action. -/
theorem controlledSwapWordCore_reference_eq_basisAction
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width)
    (input : QubitBasis (ancillaQubits + systemQubits)) :
    (TotalReversibleStage.controlledSwapWordCore layout.control
      layout.left.wires layout.right.wires).reference input =
        controlledRegisterSwapBasisAction layout.toCore input := by
  rw [controlledSwapWordCore_eq_controlledRegisterSwapStage layout]
  exact ClassicalReversibleStage.controlledRegisterSwapStage_reference_apply
    layout.toCore input

/-- A one-bit core Fredkin action is the reindexed Q swap action. -/
private theorem fredkinBasisAction_toJoint
    {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits)
    (_controlLeft : control ≠ left) (_controlRight : control ≠ right)
    (leftRight : left ≠ right)
    (input : JointBasis ancillaQubits systemQubits) :
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm
        (fredkinBasisAction
          (analyticCanonicalWireEquiv ancillaQubits systemQubits control)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits left)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits right)
          (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)) =
      if input control then ReversibleCircuit.swapBasisAction left right input
      else input := by
  funext wire
  by_cases isLeft : wire = left <;> by_cases isRight : wire = right <;>
    cases controlValue : input control <;>
    cases leftValue : input left <;> cases rightValue : input right <;>
    simp [fredkinBasisAction, ReversibleCircuit.swapBasisAction,
      analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv,
      leftRight, Ne.symm leftRight,
      isLeft, isRight, controlValue, leftValue, rightValue]

private theorem controlledSwapFold_toJoint
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width)
    (indices : List (Fin width))
    (input : JointBasis ancillaQubits systemQubits) :
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm
        (indices.foldl
          (fun state index => fredkinBasisAction layout.toCore.control
            (layout.toCore.left.wire index)
            (layout.toCore.right.wire index) state)
          (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)) =
      if input layout.control then
        ReversibleCircuit.swapPairsAction
          ((indices.map layout.left.wire).zip
            (indices.map layout.right.wire)) input
      else input := by
  induction indices generalizing input with
  | nil => simp [ReversibleCircuit.swapPairsAction]
  | cons index rest inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons, List.zip_cons_cons]
      have oneBit := fredkinBasisAction_toJoint layout.control
        (layout.left.wire index) (layout.right.wire index)
        (layout.controlLeftDifferent index)
        (layout.controlRightDifferent index)
        (layout.leftRightDisjoint index index) input
      have oneBitCore := congrArg
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits) oneBit
      simp only [Equiv.apply_symm_apply] at oneBitCore
      have oneBitCore' :
          fredkinBasisAction layout.toCore.control
              (layout.toCore.left.wire index)
              (layout.toCore.right.wire index)
              (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) =
            analyticJointBasisCoreEquiv ancillaQubits systemQubits
              (if input layout.control then
                ReversibleCircuit.swapBasisAction
                  (layout.left.wire index) (layout.right.wire index) input
              else input) := by
        simpa [ValidatedControlledRegisterSwapLayout.toCore,
          ValidatedQRegister.toCore] using oneBitCore
      rw [oneBitCore']
      cases controlValue : input layout.control with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          simpa [controlValue] using inductionHypothesis input
      | true =>
          simp only [if_true]
          rw [inductionHypothesis
            (ReversibleCircuit.swapBasisAction
              (layout.left.wire index) (layout.right.wire index) input)]
          have controlPreserved :
              ReversibleCircuit.swapBasisAction
                  (layout.left.wire index) (layout.right.wire index) input
                  layout.control =
                input layout.control :=
            ReversibleCircuit.swapBasisAction_other
              (layout.left.wire index) (layout.right.wire index)
              layout.control input (layout.controlLeftDifferent index)
                (layout.controlRightDifferent index)
          simp only [controlPreserved, controlValue, if_true,
            ReversibleCircuit.swapPairsAction]

/-- A validated controlled-register basis action is exactly the Q pair-swap
action after canonical basis reindexing. -/
theorem controlledRegisterSwapBasisAction_toJoint
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm
        (controlledRegisterSwapBasisAction layout.toCore
          (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)) =
      if input layout.control then
        ReversibleCircuit.swapPairsAction
          (layout.left.wires.zip layout.right.wires) input
      else input := by
  unfold controlledRegisterSwapBasisAction
  simpa only [ValidatedQRegister.wires] using
    controlledSwapFold_toJoint layout (List.finRange width) input

/-- The frozen swap child of one typed instruction has the swap action stored
in its shared compare--swap specification. -/
theorem controlledSwapStage_reference_eq_swapAction (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth)) :
    (BitonicTotalProgram.controlledSwapStage p instruction).toCore.reference input =
      controlledRegisterSwapBasisAction
        (compareSwapSpec p instruction member).swap input := by
  let different :=
    ReversibleCircuit.qTypedBitonicSchedule_left_ne_right p instruction member
  let layout :=
    BitonicTotalProgram.controlledSwapValidatedLayout p instruction different
  have stageEq :
      (BitonicTotalProgram.controlledSwapStage p instruction).toCore =
        TotalReversibleStage.controlledSwapWordCore layout.control
          layout.left.wires layout.right.wires := by
    unfold BitonicTotalProgram.controlledSwapStage
    rw [TotalReversibleStage.toCore_controlledSwapWord]
    rfl
  rw [stageEq, controlledSwapWordCore_reference_eq_basisAction layout input]
  rfl

/-- One frozen compare--exchange stage agrees with its shared direct action
whenever the equality-branch work register is clean. -/
theorem compareExchangeStage_reference_eq_basisAction (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : (equalityBranchSpec p instruction member).cleanInput input) :
    (BitonicTotalProgram.compareExchange p instruction).toCore.reference input =
      controlledWordCompareSwapBasisAction
        (compareSwapSpec p instruction member) input := by
  change
    (BitonicTotalProgram.controlledSwapStage p instruction).toCore.reference
        ((BitonicTotalProgram.comparisonStage p instruction).toCore.reference input) =
      controlledRegisterSwapBasisAction
        (compareSwapSpec p instruction member).swap
        (unsignedLessThanXorDirtyBasisAction
          (compareSwapSpec p instruction member).compare input)
  rw [comparisonStage_reference_eq_compareDirty p instruction member input clean]
  exact controlledSwapStage_reference_eq_swapAction p instruction member _

/-- Candidate natural values read through the canonical JointBasis/core basis
equivalence. -/
def sharedReadValues (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (word : Fin p.sortWordCount) : Nat :=
  ReversibleCircuit.qCandidateValue p
    ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input) word

/-- Clean comparison, scratch, and history sector transported to core basis. -/
structure SharedBitonicSortCleanInput (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth)) : Prop where
  compare_zero : ∀ wire ∈ analyticWiresToCore (sortCompareWorkWires p),
    input wire = false
  scratch_zero : ∀ wire ∈ analyticWiresToCore (sortAndScratchWires p),
    input wire = false
  history_zero : ∀ instruction ∈ qTypedBitonicSchedule p,
    input (historyCoreWire p instruction) = false

theorem SharedBitonicSortCleanInput.equalityBranchClean
    {p : QParameters} {input : QubitBasis (p.ancillaWidth + p.systemWidth)}
    (clean : SharedBitonicSortCleanInput p input)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    (equalityBranchSpec p instruction member).cleanInput input := by
  unfold ClassicalReversibleStage.EqualityBranchUnsignedLessThanSpec.cleanInput
  simpa only [equalityBranchSpec_equalFlags, equalityBranchSpec_scratch] using
    And.intro clean.compare_zero clean.scratch_zero

theorem SharedBitonicSortCleanInput.qCompareZero
    {p : QParameters} {input : QubitBasis (p.ancillaWidth + p.systemWidth)}
    (clean : SharedBitonicSortCleanInput p input) :
    ReversibleCircuit.readWires (sortCompareWorkWires p)
        ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input) =
      List.replicate (sortCompareWorkWires p).length false := by
  apply ReversibleCircuit.readWires_eq_replicate_false_of_forall
  intro wire member
  have coreZero := clean.compare_zero
    (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
      simpa [analyticWiresToCore] using member)
  simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using coreZero

theorem SharedBitonicSortCleanInput.qScratchZero
    {p : QParameters} {input : QubitBasis (p.ancillaWidth + p.systemWidth)}
    (clean : SharedBitonicSortCleanInput p input) :
    ∀ wire ∈ sortAndScratchWires p,
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input wire =
        false := by
  intro wire member
  have coreZero := clean.scratch_zero
    (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
      simpa [analyticWiresToCore] using member)
  simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using coreZero

theorem SharedBitonicSortCleanInput.qHistoryZero
    {p : QParameters} {input : QubitBasis (p.ancillaWidth + p.systemWidth)}
    (clean : SharedBitonicSortCleanInput p input) :
    ∀ instruction ∈ qTypedBitonicSchedule p,
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history) = false := by
  intro instruction member
  have coreZero := clean.history_zero instruction member
  simpa [historyCoreWire, analyticJointBasisCoreEquiv,
    analyticCanonicalWireEquiv] using coreZero

/-- One shared pure compare--swap action is the frozen Q step reference on the
clean work sector. -/
theorem controlledWordCompareSwapBasisAction_toJoint (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (comparisonClean : (equalityBranchSpec p instruction member).cleanInput
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input))
    (historyZero : input ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false) :
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
        (controlledWordCompareSwapBasisAction
          (compareSwapSpec p instruction member)
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)) =
      ReversibleCircuit.qBitonicStepReference p instruction input := by
  have comparison := comparisonStage_reference_toJoint p instruction member input
    comparisonClean
  rw [comparisonStage_reference_eq_compareDirty p instruction member _
    comparisonClean] at comparison
  let different := ReversibleCircuit.qTypedBitonicSchedule_left_ne_right
    p instruction member
  let layout := BitonicTotalProgram.controlledSwapValidatedLayout
    p instruction different
  have swap := controlledRegisterSwapBasisAction_toJoint layout
    ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
      (unsignedLessThanXorDirtyBasisAction
        (compareSwapSpec p instruction member).compare
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)))
  simp only [Equiv.apply_symm_apply] at swap
  unfold controlledWordCompareSwapBasisAction
  rw [show (compareSwapSpec p instruction member).swap = layout.toCore by
    simp [layout]]
  rw [swap, comparison]
  cases ascending : instruction.ascending
  · by_cases shouldSwap : ReversibleCircuit.littleEndianNat
        (ReversibleCircuit.readWires (candidateWordAt p instruction.left) input) <
      ReversibleCircuit.littleEndianNat
        (ReversibleCircuit.readWires (candidateWordAt p instruction.right) input)
    · simp [ReversibleCircuit.qBitonicStepReference, comparisonLeftWires,
        comparisonRightWires, ascending, shouldSwap, layout,
        BitonicTotalProgram.controlledSwapValidatedLayout,
        candidateValidatedRegister_wires, historyZero, xBasisAction]
    · simp [ReversibleCircuit.qBitonicStepReference, comparisonLeftWires,
        comparisonRightWires, ascending, shouldSwap, layout,
        BitonicTotalProgram.controlledSwapValidatedLayout,
        historyZero]
  · by_cases shouldSwap : ReversibleCircuit.littleEndianNat
        (ReversibleCircuit.readWires (candidateWordAt p instruction.right) input) <
      ReversibleCircuit.littleEndianNat
        (ReversibleCircuit.readWires (candidateWordAt p instruction.left) input)
    · simp [ReversibleCircuit.qBitonicStepReference, comparisonLeftWires,
        comparisonRightWires, ascending, shouldSwap, layout,
        BitonicTotalProgram.controlledSwapValidatedLayout,
        candidateValidatedRegister_wires, historyZero, xBasisAction]
    · simp [ReversibleCircuit.qBitonicStepReference, comparisonLeftWires,
        comparisonRightWires, ascending, shouldSwap, layout,
        BitonicTotalProgram.controlledSwapValidatedLayout,
        historyZero]

private theorem equalityBranchClean_of_qZero
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (compareZero : ∀ wire ∈ sortCompareWorkWires p, input wire = false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false) :
    (equalityBranchSpec p instruction member).cleanInput
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) := by
  unfold ClassicalReversibleStage.EqualityBranchUnsignedLessThanSpec.cleanInput
  constructor
  · rw [equalityBranchSpec_equalFlags]
    intro coreWire coreMember
    rcases List.mem_map.mp coreMember with ⟨wire, wireMember, rfl⟩
    simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using
      compareZero wire wireMember
  · rw [equalityBranchSpec_scratch]
    intro coreWire coreMember
    rcases List.mem_map.mp coreMember with ⟨wire, wireMember, rfl⟩
    simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using
      scratchZero wire wireMember

private theorem qBitonicStepReference_preserves_compare_wire
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ sortCompareWorkWires p) :
    ReversibleCircuit.qBitonicStepReference p instruction input wire = input wire := by
  apply ReversibleCircuit.qBitonicStepReference_other p instruction input wire
  · intro candidateMember
    exact (List.disjoint_left.mp
      (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p instruction.left)
        candidateMember) member
  · intro candidateMember
    exact (List.disjoint_left.mp
      (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p instruction.right)
        candidateMember) member
  · intro equal
    subst wire
    exact ReversibleCircuit.sortHistoryWire_not_mem_compare p
      instruction.history member

private def compareSwapSpecsFor (p : QParameters)
    (schedule : List
      (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (allMembers : ∀ instruction ∈ schedule,
      instruction ∈ qTypedBitonicSchedule p) :
    List (ControlledWordCompareSwapSpec (p.ancillaWidth + p.systemWidth)
      (p.wordWidth + 1)) :=
  schedule.attach.map fun entry =>
    compareSwapSpec p entry.1 (allMembers entry.1 entry.2)

@[simp] private theorem compareSwapSpecsFor_nil (p : QParameters)
    (allMembers : ∀ instruction ∈ ([] : List
      (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)),
      instruction ∈ qTypedBitonicSchedule p) :
    compareSwapSpecsFor p [] allMembers = [] := rfl

@[simp] private theorem compareSwapSpecsFor_cons (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (schedule : List
      (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (allMembers : ∀ next ∈ instruction :: schedule,
      next ∈ qTypedBitonicSchedule p) :
    compareSwapSpecsFor p (instruction :: schedule) allMembers =
      compareSwapSpec p instruction (allMembers instruction (by simp)) ::
        compareSwapSpecsFor p schedule
          (fun next member => allMembers next (by simp [member])) := by
  simp [compareSwapSpecsFor]

private theorem bitonicCompareSwapSequenceBasisAction_specsFor
    (p : QParameters) :
    ∀ (schedule : List
        (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
      (allMembers : ∀ instruction ∈ schedule,
        instruction ∈ qTypedBitonicSchedule p)
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (schedule.map (fun instruction => instruction.history)).Nodup →
      (∀ wire ∈ sortCompareWorkWires p, input wire = false) →
      (∀ wire ∈ sortAndScratchWires p, input wire = false) →
      (∀ instruction ∈ schedule,
        input ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history) = false) →
      bitonicCompareSwapSequenceBasisAction
          (compareSwapSpecsFor p schedule allMembers)
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) =
        analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth
          (ReversibleCircuit.CanonicalCandidateSortWithHistoryRestorationSpec
            p schedule input) := by
  intro schedule
  induction schedule with
  | nil =>
      intro allMembers input _ _ _ _
      rfl
  | cons instruction schedule inductionHypothesis =>
      intro allMembers input historyNodup compareZero scratchZero historiesZero
      have instructionMember := allMembers instruction (by simp)
      have scheduleMembers : ∀ next ∈ schedule,
          next ∈ qTypedBitonicSchedule p := by
        intro next member
        exact allMembers next (by simp [member])
      have historySplit := List.nodup_cons.mp historyNodup
      have comparisonClean := equalityBranchClean_of_qZero p instruction
        instructionMember input compareZero scratchZero
      have step := controlledWordCompareSwapBasisAction_toJoint p instruction
        instructionMember input comparisonClean
          (historiesZero instruction (by simp))
      have stepCore := congrArg
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth) step
      simp only [Equiv.apply_symm_apply] at stepCore
      rw [compareSwapSpecsFor_cons,
        bitonicCompareSwapSequenceBasisAction_cons, stepCore]
      apply inductionHypothesis scheduleMembers
        (ReversibleCircuit.qBitonicStepReference p instruction input)
        historySplit.2
      · intro wire member
        rw [qBitonicStepReference_preserves_compare_wire p instruction input
          wire member]
        exact compareZero wire member
      · intro wire member
        rw [ReversibleCircuit.qBitonicStepReference_preserves_scratch
          p instruction input wire member]
        exact scratchZero wire member
      · intro next nextMember
        have different : next.history ≠ instruction.history := by
          intro equal
          apply historySplit.1
          exact List.mem_map.mpr ⟨next, nextMember, equal⟩
        rw [ReversibleCircuit.qBitonicStepReference_preserves_other_history
          p instruction next different input]
        exact historiesZero next (by simp [nextMember])

private theorem sortStageReference_specsFor
    (p : QParameters) :
    ∀ (schedule : List
        (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
      (_allMembers : ∀ instruction ∈ schedule,
        instruction ∈ qTypedBitonicSchedule p)
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (schedule.map (fun instruction => instruction.history)).Nodup →
      (∀ wire ∈ sortCompareWorkWires p, input wire = false) →
      (∀ wire ∈ sortAndScratchWires p, input wire = false) →
      (∀ instruction ∈ schedule,
        input ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history) = false) →
      (TotalReversibleStage.sequence
          (schedule.map (BitonicTotalProgram.compareExchange p))).toCore.reference
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) =
        analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth
          (ReversibleCircuit.CanonicalCandidateSortWithHistoryRestorationSpec
            p schedule input) := by
  intro schedule
  induction schedule with
  | nil =>
      intro allMembers input _ _ _ _
      rfl
  | cons instruction schedule inductionHypothesis =>
      intro allMembers input historyNodup compareZero scratchZero historiesZero
      have instructionMember := allMembers instruction (by simp)
      have scheduleMembers : ∀ next ∈ schedule,
          next ∈ qTypedBitonicSchedule p := by
        intro next member
        exact allMembers next (by simp [member])
      have historySplit := List.nodup_cons.mp historyNodup
      have comparisonClean := equalityBranchClean_of_qZero p instruction
        instructionMember input compareZero scratchZero
      have strictStep := compareExchangeStage_reference_eq_basisAction
        p instruction instructionMember
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)
          comparisonClean
      have pureStep := controlledWordCompareSwapBasisAction_toJoint p instruction
        instructionMember input comparisonClean
          (historiesZero instruction (by simp))
      have pureStepCore := congrArg
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth) pureStep
      simp only [Equiv.apply_symm_apply] at pureStepCore
      have stepCorrect :
          (BitonicTotalProgram.compareExchange p instruction).toCore.reference
              (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) =
            analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth
              (ReversibleCircuit.qBitonicStepReference p instruction input) :=
        strictStep.trans pureStepCore
      change
        (TotalReversibleStage.sequence
          (schedule.map (BitonicTotalProgram.compareExchange p))).toCore.reference
            ((BitonicTotalProgram.compareExchange p instruction).toCore.reference
              (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)) = _
      rw [stepCorrect]
      apply inductionHypothesis scheduleMembers
        (ReversibleCircuit.qBitonicStepReference p instruction input)
        historySplit.2
      · intro wire member
        rw [qBitonicStepReference_preserves_compare_wire p instruction input
          wire member]
        exact compareZero wire member
      · intro wire member
        rw [ReversibleCircuit.qBitonicStepReference_preserves_scratch
          p instruction input wire member]
        exact scratchZero wire member
      · intro next nextMember
        have different : next.history ≠ instruction.history := by
          intro equal
          apply historySplit.1
          exact List.mem_map.mpr ⟨next, nextMember, equal⟩
        rw [ReversibleCircuit.qBitonicStepReference_preserves_other_history
          p instruction next different input]
        exact historiesZero next (by simp [nextMember])

/-- Comparison and multi-control work is restored after the full sort. -/
def sharedWorkRestored (p : QParameters)
    (output : QubitBasis (p.ancillaWidth + p.systemWidth)) : Prop :=
  (∀ wire ∈ analyticWiresToCore (sortCompareWorkWires p),
      output wire = false) ∧
    ∀ wire ∈ analyticWiresToCore (sortAndScratchWires p),
      output wire = false

/-- Every wire outside candidate words and allocated history is preserved. -/
def sharedRestoration (p : QParameters)
    (input output : QubitBasis (p.ancillaWidth + p.systemWidth)) : Prop :=
  ∀ wire,
    (∀ word : Fin p.sortWordCount, wire ∉ candidateWordAt p word) →
    (∀ instruction ∈ qTypedBitonicSchedule p,
      wire ≠ (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) →
    ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm output)
        wire =
      ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input)
        wire

/-- The existing Q pure sort reference transported to canonical core basis. -/
def sharedCanonicalReference (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth)) :
    QubitBasis (p.ancillaWidth + p.systemWidth) :=
  analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth
    (ReversibleCircuit.CanonicalCandidateSortWithHistoryRestorationSpec p
      (qTypedBitonicSchedule p)
      ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input))

/-- The full shared pure sequence is the independent frozen Q reference on the
clean sector. -/
theorem bitonicCompareSwapSequenceBasisAction_eq_sharedCanonicalReference
    (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : SharedBitonicSortCleanInput p input) :
    bitonicCompareSwapSequenceBasisAction (compareSwapSpecs p) input =
      sharedCanonicalReference p input := by
  let qInput :=
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input
  have compareZero : ∀ wire ∈ sortCompareWorkWires p,
      qInput wire = false := by
    intro wire member
    have coreZero := clean.compare_zero
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
        simpa [analyticWiresToCore] using member)
    simpa [qInput, analyticJointBasisCoreEquiv,
      analyticCanonicalWireEquiv] using coreZero
  have scratchZero : ∀ wire ∈ sortAndScratchWires p,
      qInput wire = false := by
    intro wire member
    have coreZero := clean.scratch_zero
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
        simpa [analyticWiresToCore] using member)
    simpa [qInput, analyticJointBasisCoreEquiv,
      analyticCanonicalWireEquiv] using coreZero
  let allMembers : ∀ instruction ∈ qTypedBitonicSchedule p,
      instruction ∈ qTypedBitonicSchedule p := fun _ member => member
  have sequenceCorrect := bitonicCompareSwapSequenceBasisAction_specsFor p
    (qTypedBitonicSchedule p) allMembers qInput
      (ReversibleCircuit.qTypedBitonicSchedule_history_nodup p)
      compareZero scratchZero (by
        intro instruction member
        simpa [qInput] using clean.qHistoryZero instruction member)
  simpa [compareSwapSpecs, compareSwapSpecsFor, sharedCanonicalReference,
    qInput, allMembers] using sequenceCorrect

/-- The independent frozen strict sort stage has the same clean reference. -/
theorem sortCanonicalCoreReference_eq_sharedCanonicalReference
    (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : SharedBitonicSortCleanInput p input) :
    (BitonicTotalProgram.sort p).toCore.reference input =
      sharedCanonicalReference p input := by
  let qInput :=
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input
  have compareZero : ∀ wire ∈ sortCompareWorkWires p,
      qInput wire = false := by
    intro wire member
    have coreZero := clean.compare_zero
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
        simpa [analyticWiresToCore] using member)
    simpa [qInput, analyticJointBasisCoreEquiv,
      analyticCanonicalWireEquiv] using coreZero
  have scratchZero : ∀ wire ∈ sortAndScratchWires p,
      qInput wire = false := by
    intro wire member
    have coreZero := clean.scratch_zero
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
        simpa [analyticWiresToCore] using member)
    simpa [qInput, analyticJointBasisCoreEquiv,
      analyticCanonicalWireEquiv] using coreZero
  let allMembers : ∀ instruction ∈ qTypedBitonicSchedule p,
      instruction ∈ qTypedBitonicSchedule p := fun _ member => member
  have sequenceCorrect := sortStageReference_specsFor p
    (qTypedBitonicSchedule p) allMembers qInput
      (ReversibleCircuit.qTypedBitonicSchedule_history_nodup p)
      compareZero scratchZero (by
        intro instruction member
        simpa [qInput] using clean.qHistoryZero instruction member)
  simpa [BitonicTotalProgram.sort, BitonicTotalProgram.qSchedule_eq,
    sharedCanonicalReference, qInput, allMembers] using sequenceCorrect

/-- Joint-basis view of the frozen sort reference, derived from the canonical
core strict reference transport. -/
theorem sortReference_eq_canonicalCandidateReference
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : SharedBitonicSortCleanInput p
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)) :
    (BitonicTotalProgram.sort p).reference input =
      ReversibleCircuit.CanonicalCandidateSortWithHistoryRestorationSpec p
        (qTypedBitonicSchedule p) input := by
  apply (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).injective
  rw [← TotalReversibleStage.toCore_reference_apply]
  simpa [sharedCanonicalReference] using
    sortCanonicalCoreReference_eq_sharedCanonicalReference p
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) clean

theorem sharedReadValues_canonicalReference (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth)) :
    sharedReadValues p (sharedCanonicalReference p input) =
      runTypedBitonicValues (qTypedBitonicSchedule p)
        (sharedReadValues p input) := by
  unfold sharedReadValues sharedCanonicalReference
  simp only [Equiv.symm_apply_apply]
  rw [ReversibleCircuit.qCandidateValue_canonicalCandidateSortWithHistoryRestorationSpec p
      (qTypedBitonicSchedule p)
      ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input)
      (by intro instruction member; exact member)]
  exact ReversibleCircuit.qBitonicValuesReference_eq_typed p
    (qTypedBitonicSchedule p)
    (ReversibleCircuit.qCandidateValue p
      ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input))

theorem sharedRestoration_canonicalReference (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth)) :
    sharedRestoration p input (sharedCanonicalReference p input) := by
  intro wire outsideCandidates outsideHistories
  simp only [sharedCanonicalReference, Equiv.symm_apply_apply]
  exact ReversibleCircuit.canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p
      (qTypedBitonicSchedule p)
      ((analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm input)
      wire outsideCandidates outsideHistories

theorem sharedWorkRestored_canonicalReference (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : SharedBitonicSortCleanInput p input) :
    sharedWorkRestored p (sharedCanonicalReference p input) := by
  constructor
  · intro coreWire coreMember
    rcases List.mem_map.mp coreMember with ⟨wire, wireMember, rfl⟩
    have preserved := sharedRestoration_canonicalReference p input wire
      (by
        intro word candidateMember
        exact (List.disjoint_left.mp
          (ReversibleCircuit.sortCandidateWordAt_disjoint_compare p word))
            candidateMember wireMember)
      (by
        intro instruction _ equal
        subst wire
        exact ReversibleCircuit.sortHistoryWire_not_mem_compare p
          instruction.history wireMember)
    have inputZero := clean.compare_zero
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
        simpa [analyticWiresToCore] using wireMember)
    have preservedCore :
        sharedCanonicalReference p input
            (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) =
          input (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) := by
      simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using preserved
    exact preservedCore.trans inputZero
  · intro coreWire coreMember
    rcases List.mem_map.mp coreMember with ⟨wire, wireMember, rfl⟩
    have preserved := sharedRestoration_canonicalReference p input wire
      (by
        intro word candidateMember
        exact (List.disjoint_left.mp
          (ReversibleCircuit.sortCandidateWordAt_disjoint_scratch p word))
            candidateMember wireMember)
      (by
        intro instruction _ equal
        subst wire
        exact ReversibleCircuit.sortHistoryWire_not_mem_scratch p
          instruction.history wireMember)
    have inputZero := clean.scratch_zero
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) (by
        simpa [analyticWiresToCore] using wireMember)
    have preservedCore :
        sharedCanonicalReference p input
            (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) =
          input (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth wire) := by
      simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using preserved
    exact preservedCore.trans inputZero

theorem compareSwapSpecs_length (p : QParameters) :
    (qTypedBitonicSchedule p).length = (compareSwapSpecs p).length := by
  simp [compareSwapSpecs]

theorem sharedSchedule_sorts (p : QParameters)
    (values : Fin p.sortWordCount → Nat) :
    IsSortedFin (runTypedBitonicValues (qTypedBitonicSchedule p) values) :=
  qTypedBitonicSchedule_sorts_nat p values

/-- Assemble the shared clean plan once the frozen pure stage has been
identified with the shared compare--swap reference on the clean sector. -/
private def sharedBitonicSortCleanPlanOfReferenceCorrect (p : QParameters)
    (referenceCorrect : ∀ input, SharedBitonicSortCleanInput p input →
      bitonicCompareSwapSequenceBasisAction (compareSwapSpecs p) input =
        sharedCanonicalReference p input) :
    BitonicCompareSwapCleanPlan (p.ancillaWidth + p.systemWidth)
      (p.wordWidth + 1) p.sortWordCount p.sortFlagWidth where
  specs := compareSwapSpecs p
  schedule := qTypedBitonicSchedule p
  scheduleLength_eq_specs := compareSwapSpecs_length p
  readValues := sharedReadValues p
  cleanInput := SharedBitonicSortCleanInput p
  workRestored := sharedWorkRestored p
  restoration := sharedRestoration p
  readValues_correct := by
    intro input clean
    rw [referenceCorrect input clean]
    exact sharedReadValues_canonicalReference p input
  schedule_sorts := sharedSchedule_sorts p
  workRestored_correct := by
    intro input clean
    rw [referenceCorrect input clean]
    exact sharedWorkRestored_canonicalReference p input clean
  restoration_correct := by
    intro input clean
    rw [referenceCorrect input clean]
    exact sharedRestoration_canonicalReference p input

/-- Canonical shared clean bitonic plan for the frozen Q layout. -/
noncomputable def sharedBitonicSortCleanPlan (p : QParameters) :
    BitonicCompareSwapCleanPlan (p.ancillaWidth + p.systemWidth)
      (p.wordWidth + 1) p.sortWordCount p.sortFlagWidth :=
  sharedBitonicSortCleanPlanOfReferenceCorrect p
    (bitonicCompareSwapSequenceBasisAction_eq_sharedCanonicalReference p)

/-- The frozen full-space Exact sort target acts as the shared independent
clean plan reference on clean basis states. -/
theorem sortCanonicalCoreExactComponent_basisKet (p : QParameters)
    (input : QubitBasis (p.ancillaWidth + p.systemWidth))
    (clean : (sharedBitonicSortCleanPlan p).cleanInput input) :
    applyOperator (BitonicTotalProgram.sortCanonicalCoreExactComponent p).target
        (basisKet input) =
      basisKet ((sharedBitonicSortCleanPlan p).reference input) := by
  change applyOperator (BitonicTotalProgram.sortCanonicalCoreAnalyticOperator p)
      (basisKet input) = _
  rw [show BitonicTotalProgram.sortCanonicalCoreAnalyticOperator p =
      (BitonicTotalProgram.sort p).toCore.analyticOperator by
    exact TotalReversibleStage.reindex_analyticOperator_eq_toCore
      (BitonicTotalProgram.sort p)]
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference]
  change VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.deterministicOperator
      (fun basis => (BitonicTotalProgram.sort p).toCore.reference basis))
        (VerifiedCircuitCore.basisKet input) = _
  rw [VerifiedCircuitCore.applyOperator_deterministicOperator_basisKet]
  apply congrArg basisKet
  have strictReference := sortCanonicalCoreReference_eq_sharedCanonicalReference
    p input clean
  have planReference :=
    bitonicCompareSwapSequenceBasisAction_eq_sharedCanonicalReference p input clean
  exact strictReference.trans planReference.symm

/-- Shared coherent clean parent built only from the frozen full-space Exact
child and the independent pure plan transport. -/
noncomputable def sharedBitonicSortCleanSubspaceMapComponent (p : QParameters) :
    SubspaceMapComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment) :=
  bitonicCompareSwapSequenceCleanSubspaceMapComponentOfExact internalZeroSymbolEnvironment
    (sharedBitonicSortCleanPlan p)
    (BitonicTotalProgram.sortCanonicalCoreExactComponent p)
    (sortCanonicalCoreExactComponent_basisKet p)

end BitonicSharedClean

end

end ProbabilityGeneratorQProof
