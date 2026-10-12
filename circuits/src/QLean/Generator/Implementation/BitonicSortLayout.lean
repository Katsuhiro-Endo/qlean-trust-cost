import QLean.Generator.Analysis.BitonicTotalStage
import QLean.Generator.Implementation.ReversibleArithmetic

/-!
# Q bitonic wire layout and frozen compiler

The recursive schedule is the shared-core schedule exposed by
`BitonicTotalProgram.qSchedule`.  This module contains only the Q register
layout and the frozen reversible AST constructors.
-/

namespace ProbabilityGeneratorQProof

/-- The canonical Q schedule is the shared typed bitonic schedule. -/
def qTypedBitonicSchedule (p : QParameters) :
    List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :=
  BitonicTotalProgram.qSchedule p

/-- Physical wire of one bit in one padded candidate word. -/
def candidateWordWire (p : QParameters)
    (word : Fin p.sortWordCount) (bit : Fin (p.wordWidth + 1)) :
    Wire p.ancillaWidth p.systemWidth :=
  let localIndex : Fin p.candidateWidth :=
    ⟨word.val * (p.wordWidth + 1) + bit.val, by
      simp only [QParameters.candidateWidth]
      nlinarith [word.isLt, bit.isLt]⟩
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).ancillaWire
    localIndex

/-- All padded candidate words in canonical order. -/
def candidateWords (p : QParameters) :
    List (List (Wire p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.sortWordCount).map fun word =>
    (List.finRange (p.wordWidth + 1)).map fun bit => candidateWordWire p word bit

/-- One padded candidate word at a typed index. -/
def candidateWordAt (p : QParameters) (word : Fin p.sortWordCount) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange (p.wordWidth + 1)).map fun bit => candidateWordWire p word bit

/-- Marker bit of one padded candidate word. -/
def candidateMarkerWire (p : QParameters) (word : Fin p.sortWordCount) :
    Wire p.ancillaWidth p.systemWidth :=
  candidateWordWire p word ⟨p.wordWidth, by omega⟩

/-- Canonical history-wire list for the bitonic comparator. -/
def sortHistoryWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.sortFlagWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).sortFlags).ancillaWire
      index

/-- Canonical equality/comparison work wires. -/
def sortCompareWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  let comparison := (List.finRange p.wordWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork).ancillaWire
      index
  let extra :=
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire
      ⟨0, by simp [QParameters.andWorkWidth]⟩
  comparison ++ [extra]

/-- Canonical multi-control scratch wires. -/
def sortAndScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange (p.andWorkWidth - 1)).map fun index =>
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).andWork).ancillaWire
        ⟨index.val + 1, by
          simp [QParameters.andWorkWidth] at index ⊢
          omega⟩

/-- Compile one typed compare-exchange at the Q layout. -/
def emitTypedBitonicCompareExchange
    {ancillaQubits systemQubits wordCount historyCount : Nat}
    (word : Fin wordCount → List (Wire ancillaQubits systemQubits))
    (equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (history : Wire ancillaQubits systemQubits)
    (instruction : TypedBitonicCompareExchange wordCount historyCount) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let left := word instruction.left
  let right := word instruction.right
  let compare := if instruction.ascending then
    ReversibleCircuit.xorLessThanIntoTargetCircuit right left equalFlags scratch
      history
  else
    ReversibleCircuit.xorLessThanIntoTargetCircuit left right equalFlags scratch
      history
  .seq compare (ReversibleCircuit.controlledSwapWord history left right)

/-- Compile a typed schedule while preserving its source order. -/
def emitTypedBitonicSort
    {ancillaQubits systemQubits wordCount historyCount : Nat}
    (word : Fin wordCount → List (Wire ancillaQubits systemQubits))
    (equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (history : Fin historyCount → Wire ancillaQubits systemQubits)
    (schedule : List (TypedBitonicCompareExchange wordCount historyCount)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| schedule.map fun instruction =>
    emitTypedBitonicCompareExchange word equalFlags scratch
      (history instruction.history) instruction

/-- Frozen Q candidate-sort AST. -/
def reversiblySortCandidateWordsAndRestoreHistoryCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  emitTypedBitonicSort (candidateWordAt p) (sortCompareWorkWires p)
    (sortAndScratchWires p)
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).sortFlags).ancillaWire
    (qTypedBitonicSchedule p)

end ProbabilityGeneratorQProof
