import QLean.Circuits.Foundation.ReversibleLogicAnalytic

/-!
# Pure bitonic schedules and compare-swap semantics

The schedule is independent of physical wires.  A physical compare-swap is
described only by reusable unsigned-comparison and controlled-register-swap
specifications.
-/

namespace VerifiedCircuitCore

/-- A layout-independent compare-exchange instruction. -/
structure BitonicCompareExchange (wordCount : Nat) where
  left : Fin wordCount
  right : Fin wordCount
  ascending : Bool
deriving DecidableEq, Repr

/-- A compare-exchange instruction with a typed history slot. -/
structure BitonicCompareExchangeWithHistory
    (wordCount historyCount : Nat) extends BitonicCompareExchange wordCount where
  history : Fin historyCount
deriving DecidableEq, Repr

/-- Width of the recursive bitonic network at a given level. -/
def bitonicNetworkWidth : Nat → Nat
  | 0 => 1
  | level + 1 => 2 * bitonicNetworkWidth level

theorem bitonicNetworkWidth_eq_pow (level : Nat) :
    bitonicNetworkWidth level = 2 ^ level := by
  induction level with
  | zero => rfl
  | succ level inductionHypothesis =>
      simp [bitonicNetworkWidth, inductionHypothesis, pow_succ, Nat.mul_comm]

theorem bitonicNetworkWidth_pos (level : Nat) :
    0 < bitonicNetworkWidth level := by
  rw [bitonicNetworkWidth_eq_pow]
  positivity

/-- Embed an instruction into the left half of a doubled network. -/
def BitonicCompareExchange.liftLeft {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    BitonicCompareExchange (2 * wordCount) where
  left := ⟨instruction.left.val, by omega⟩
  right := ⟨instruction.right.val, by omega⟩
  ascending := instruction.ascending

/-- Embed an instruction into the right half of a doubled network. -/
def BitonicCompareExchange.liftRight {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    BitonicCompareExchange (2 * wordCount) where
  left := ⟨instruction.left.val + wordCount, by omega⟩
  right := ⟨instruction.right.val + wordCount, by omega⟩
  ascending := instruction.ascending

@[simp] theorem BitonicCompareExchange.liftLeft_left_val {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    instruction.liftLeft.left.val = instruction.left.val := rfl

@[simp] theorem BitonicCompareExchange.liftLeft_right_val {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    instruction.liftLeft.right.val = instruction.right.val := rfl

@[simp] theorem BitonicCompareExchange.liftLeft_ascending {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    instruction.liftLeft.ascending = instruction.ascending := rfl

@[simp] theorem BitonicCompareExchange.liftRight_left_val {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    instruction.liftRight.left.val = instruction.left.val + wordCount := rfl

@[simp] theorem BitonicCompareExchange.liftRight_right_val {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    instruction.liftRight.right.val = instruction.right.val + wordCount := rfl

@[simp] theorem BitonicCompareExchange.liftRight_ascending {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    instruction.liftRight.ascending = instruction.ascending := rfl

/-- The top half-cleaner of a recursive bitonic merge. -/
def bitonicHalfCleaner (level : Nat) (ascending : Bool) :
    List (BitonicCompareExchange (2 * bitonicNetworkWidth level)) :=
  (List.finRange (bitonicNetworkWidth level)).map fun index =>
    { left := ⟨index.val, by omega⟩
      right := ⟨index.val + bitonicNetworkWidth level, by omega⟩
      ascending := ascending }

/-- Recursive bitonic merge schedule. -/
def bitonicMergeSchedule :
    (level : Nat) → (ascending : Bool) →
      List (BitonicCompareExchange (bitonicNetworkWidth level))
  | 0, _ => []
  | level + 1, ascending =>
      bitonicHalfCleaner level ascending ++
        (bitonicMergeSchedule level ascending).map
          BitonicCompareExchange.liftLeft ++
        (bitonicMergeSchedule level ascending).map
          BitonicCompareExchange.liftRight

/-- Batcher bitonic sorting schedule on `2^level` words. -/
def bitonicSortSchedule :
    (level : Nat) → (ascending : Bool) →
      List (BitonicCompareExchange (bitonicNetworkWidth level))
  | 0, _ => []
  | level + 1, ascending =>
      let merge : List
          (BitonicCompareExchange (2 * bitonicNetworkWidth level)) := by
        simpa [bitonicNetworkWidth] using
          bitonicMergeSchedule (level + 1) ascending
      (bitonicSortSchedule level true).map BitonicCompareExchange.liftLeft ++
        (bitonicSortSchedule level false).map BitonicCompareExchange.liftRight ++
        merge

/-- A simple capacity bound for the recursive merge schedule. -/
theorem bitonicMergeSchedule_length_le (level : Nat) (ascending : Bool) :
    (bitonicMergeSchedule level ascending).length ≤
      bitonicNetworkWidth level * level := by
  induction level generalizing ascending with
  | zero => simp [bitonicMergeSchedule]
  | succ level inductionHypothesis =>
      have previous := inductionHypothesis ascending
      simp only [bitonicMergeSchedule, List.length_append, List.length_map,
        bitonicHalfCleaner, List.length_finRange, bitonicNetworkWidth]
      nlinarith

/-- The standard history capacity used by recursive consumers is sufficient
for every compare-exchange in the sorting schedule. -/
theorem bitonicSortSchedule_length_le_historyCapacity
    (level : Nat) (ascending : Bool) :
    (bitonicSortSchedule level ascending).length ≤
      bitonicNetworkWidth level * (level + 1) ^ 2 := by
  induction level generalizing ascending with
  | zero => simp [bitonicSortSchedule]
  | succ level inductionHypothesis =>
      have leftBound := inductionHypothesis true
      have rightBound := inductionHypothesis false
      have mergeBound := bitonicMergeSchedule_length_le (level + 1) ascending
      simp only [bitonicSortSchedule, List.length_append, List.length_map,
        bitonicNetworkWidth]
      simp only [bitonicNetworkWidth] at mergeBound
      nlinarith

/-- Cast a schedule instruction along a word-count equality. -/
def BitonicCompareExchange.cast {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (instruction : BitonicCompareExchange sourceWidth) :
    BitonicCompareExchange targetWidth where
  left := Fin.cast widthEquality instruction.left
  right := Fin.cast widthEquality instruction.right
  ascending := instruction.ascending

/-- Attach history slots from an arbitrary offset. -/
def attachBitonicHistoryFrom {wordCount historyCount : Nat}
    (positiveHistory : 0 < historyCount) :
    Nat → List (BitonicCompareExchange wordCount) →
      List (BitonicCompareExchangeWithHistory wordCount historyCount)
  | _, [] => []
  | offset, instruction :: schedule =>
      { toBitonicCompareExchange := instruction
        history := ⟨offset % historyCount, Nat.mod_lt _ positiveHistory⟩ } ::
      attachBitonicHistoryFrom positiveHistory (offset + 1) schedule

@[simp] theorem attachBitonicHistoryFrom_length
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (offset : Nat) (schedule : List (BitonicCompareExchange wordCount)) :
    (attachBitonicHistoryFrom positiveHistory offset schedule).length =
      schedule.length := by
  induction schedule generalizing offset with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp [attachBitonicHistoryFrom, inductionHypothesis]

/-- When a source-order schedule fits in the history register, every assigned
history value lies in its exact offset interval. -/
theorem attachBitonicHistoryFrom_history_bounds
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount) :
    ∀ (offset : Nat) (schedule : List (BitonicCompareExchange wordCount)),
      offset + schedule.length ≤ historyCount →
      ∀ instruction ∈ attachBitonicHistoryFrom positiveHistory offset schedule,
        offset ≤ instruction.history.val ∧
          instruction.history.val < offset + schedule.length := by
  intro offset schedule fits
  induction schedule generalizing offset with
  | nil => simp [attachBitonicHistoryFrom]
  | cons source schedule inductionHypothesis =>
      intro instruction member
      simp only [attachBitonicHistoryFrom, List.mem_cons] at member
      rcases member with equal | tailMember
      · subst instruction
        have offsetLt : offset < historyCount := by
          simpa using lt_of_lt_of_le
            (Nat.lt_add_of_pos_right (Nat.succ_pos schedule.length)) fits
        simp [Nat.mod_eq_of_lt offsetLt]
      · have tailFits : offset + 1 + schedule.length ≤ historyCount := by
          change offset + (schedule.length + 1) ≤ historyCount at fits
          omega
        have bounds := inductionHypothesis (offset + 1) tailFits
          instruction tailMember
        constructor
        · omega
        · change instruction.history.val < offset + (schedule.length + 1)
          omega

/-- A fitting source-order schedule receives pairwise distinct history slots. -/
theorem attachBitonicHistoryFrom_history_nodup
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount) :
    ∀ (offset : Nat) (schedule : List (BitonicCompareExchange wordCount)),
      offset + schedule.length ≤ historyCount →
      ((attachBitonicHistoryFrom positiveHistory offset schedule).map
        (fun instruction => instruction.history)).Nodup := by
  intro offset schedule fits
  induction schedule generalizing offset with
  | nil => simp [attachBitonicHistoryFrom]
  | cons source schedule inductionHypothesis =>
      have offsetLt : offset < historyCount := by
        simpa using lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (Nat.succ_pos schedule.length)) fits
      have tailFits : offset + 1 + schedule.length ≤ historyCount := by
        change offset + (schedule.length + 1) ≤ historyCount at fits
        omega
      simp only [attachBitonicHistoryFrom, List.map_cons, List.nodup_cons]
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨instruction, instructionMember,
          historyEqual⟩
        have bounds := attachBitonicHistoryFrom_history_bounds positiveHistory
          (offset + 1) schedule tailFits instruction instructionMember
        have valueEqual := congrArg Fin.val historyEqual
        simp only [Nat.mod_eq_of_lt offsetLt] at valueEqual
        omega
      · exact inductionHypothesis (offset + 1) tailFits

/-- Attach history slots starting at zero. -/
def attachBitonicHistory {wordCount historyCount : Nat}
    (positiveHistory : 0 < historyCount)
    (schedule : List (BitonicCompareExchange wordCount)) :
    List (BitonicCompareExchangeWithHistory wordCount historyCount) :=
  attachBitonicHistoryFrom positiveHistory 0 schedule

@[simp] theorem attachBitonicHistory_length
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (schedule : List (BitonicCompareExchange wordCount)) :
    (attachBitonicHistory positiveHistory schedule).length = schedule.length := by
  simp [attachBitonicHistory]

/-- A schedule that fits the history register receives pairwise distinct
history slots from zero. -/
theorem attachBitonicHistory_history_nodup
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (schedule : List (BitonicCompareExchange wordCount))
    (fits : schedule.length ≤ historyCount) :
    ((attachBitonicHistory positiveHistory schedule).map
      (fun instruction => instruction.history)).Nodup := by
  exact attachBitonicHistoryFrom_history_nodup positiveHistory 0 schedule
    (by simpa using fits)

/-- Every history slot assigned to a fitting schedule lies below the schedule
length, so an application needs no additional modular-arithmetic argument. -/
theorem attachBitonicHistory_history_lt_length
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (schedule : List (BitonicCompareExchange wordCount))
    (fits : schedule.length ≤ historyCount)
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (member : instruction ∈ attachBitonicHistory positiveHistory schedule) :
    instruction.history.val < schedule.length := by
  simpa using
    (attachBitonicHistoryFrom_history_bounds positiveHistory 0 schedule
      (by simpa using fits) instruction member).2

/-- Physical operands for one compare-then-controlled-swap stage. -/
structure ControlledWordCompareSwapSpec (qubits width : Nat) where
  ascending : Bool
  compare : UnsignedLessThanXorSpec qubits width
  swap : ControlledRegisterSwapSpec qubits width
  compareTarget_eq_swapControl : compare.target = swap.control
  compareOperands_eq_swapOperands :
    if ascending then
      compare.lhs = swap.right ∧ compare.rhs = swap.left
    else
      compare.lhs = swap.left ∧ compare.rhs = swap.right

/-- Direct full-basis action of compare, history XOR, then controlled swap. -/
def controlledWordCompareSwapBasisAction {qubits width : Nat}
    (spec : ControlledWordCompareSwapSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  controlledRegisterSwapBasisAction spec.swap
    (unsignedLessThanXorDirtyBasisAction spec.compare input)

/-- Independent deterministic operator for one controlled word compare-swap. -/
def controlledWordCompareSwapOperator {qubits width : Nat}
    (spec : ControlledWordCompareSwapSpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (controlledWordCompareSwapBasisAction spec)

/-- Direct basis action of a finite compare-swap sequence. -/
def bitonicCompareSwapSequenceBasisAction {qubits width : Nat}
    (specs : List (ControlledWordCompareSwapSpec qubits width))
    (input : QubitBasis qubits) : QubitBasis qubits :=
  specs.foldl (fun state spec => controlledWordCompareSwapBasisAction spec state)
    input

@[simp] theorem bitonicCompareSwapSequenceBasisAction_nil
    {qubits width : Nat} (input : QubitBasis qubits) :
    bitonicCompareSwapSequenceBasisAction
      ([] : List (ControlledWordCompareSwapSpec qubits width)) input = input := rfl

@[simp] theorem bitonicCompareSwapSequenceBasisAction_cons
    {qubits width : Nat} (first : ControlledWordCompareSwapSpec qubits width)
    (rest : List (ControlledWordCompareSwapSpec qubits width))
    (input : QubitBasis qubits) :
    bitonicCompareSwapSequenceBasisAction (first :: rest) input =
      bitonicCompareSwapSequenceBasisAction rest
        (controlledWordCompareSwapBasisAction first input) := rfl

/-- Independent operator target of a finite compare-swap sequence. -/
def bitonicCompareSwapSequenceOperator {qubits width : Nat}
    (specs : List (ControlledWordCompareSwapSpec qubits width)) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (bitonicCompareSwapSequenceBasisAction specs)

end VerifiedCircuitCore
