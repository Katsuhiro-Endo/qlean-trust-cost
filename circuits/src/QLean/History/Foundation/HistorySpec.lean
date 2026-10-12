import Mathlib

namespace HistoryBlockEncoding
namespace HistorySpec

noncomputable section

/-- Finite parameters for the raw history linear system. -/
structure Parameters where
  physicalClocks : Nat
  taylorOrder : Nat
  stepSize : ℚ
  binaryLabels : Nat
  clockEnd : Nat

/-- The exact domain contract used by the definitions below. -/
def WellFormed (p : Parameters) : Prop :=
  0 < p.physicalClocks ∧
  0 < p.taylorOrder ∧
  0 ≤ p.stepSize ∧
  p.taylorOrder < p.binaryLabels ∧
  p.physicalClocks < p.clockEnd

theorem WellFormed.binaryLabels_pos {p : Parameters} (wf : WellFormed p) :
    0 < p.binaryLabels := by
  rcases wf with ⟨_, _, _, order_lt_labels, _⟩
  omega

theorem WellFormed.clockEnd_pos {p : Parameters} (wf : WellFormed p) :
    0 < p.clockEnd := by
  rcases wf with ⟨_, _, _, _, clocks_lt_end⟩
  omega

/-- A labelled model configuration. -/
structure LabelState (Configuration : Type*) (p : Parameters) where
  label : Fin p.binaryLabels
  configuration : Configuration
deriving DecidableEq, Fintype

/-- A clocked history basis state. -/
structure Index (Configuration : Type*) (p : Parameters) where
  clock : Fin p.clockEnd
  state : LabelState Configuration p
deriving DecidableEq, Fintype

/-- Taylor difference on a label/configuration block. -/
def deltaTay
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :
    Matrix (LabelState Configuration p) (LabelState Configuration p) ℚ :=
  fun output input =>
    if output.label.val = input.label.val + 1 ∧
        input.label.val < p.taylorOrder then
      -(p.stepSize / ((input.label.val + 1 : Nat) : ℚ)) *
        modelQ output.configuration input.configuration
    else
      0

/-- Idle difference on the full binary label range. -/
def deltaIdle
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters) :
    Matrix (LabelState Configuration p) (LabelState Configuration p) ℚ :=
  fun output input =>
    if output.label.val = input.label.val + 1 ∧
        output.configuration = input.configuration then
      -1
    else
      0

/-- Physical-clock aggregation sends every Taylor degree to degree zero. -/
def fSigma
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters) :
    Matrix (LabelState Configuration p) (LabelState Configuration p) ℚ :=
  fun output input =>
    if output.label.val = 0 ∧
        input.label.val ≤ p.taylorOrder ∧
        output.configuration = input.configuration then
      1
    else
      0

/-- Idle aggregation sends only the final binary degree to degree zero. -/
def fBin
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters) :
    Matrix (LabelState Configuration p) (LabelState Configuration p) ℚ :=
  fun output input =>
    if output.label.val = 0 ∧
        input.label.val + 1 = p.binaryLabels ∧
        output.configuration = input.configuration then
      1
    else
      0

/-- Identity layer on the full clock/label/configuration space. -/
def L0
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters) :
    Matrix (Index Configuration p) (Index Configuration p) ℚ :=
  fun output input => if output = input then 1 else 0

/-- Within-clock Taylor or idle difference layer. -/
def L1
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :
    Matrix (Index Configuration p) (Index Configuration p) ℚ :=
  fun output input =>
    if output.clock = input.clock then
      if output.clock.val < p.physicalClocks then
        deltaTay p modelQ output.state input.state
      else
        deltaIdle p output.state input.state
    else
      0

/-- Clock-to-clock aggregation layer with no edge after the terminal clock. -/
def L2
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters) :
    Matrix (Index Configuration p) (Index Configuration p) ℚ :=
  fun output input =>
    if output.clock.val = input.clock.val + 1 then
      if input.clock.val < p.physicalClocks then
        -(fSigma p output.state input.state)
      else
        -(fBin p output.state input.state)
    else
      0

/-- Raw history matrix, defined before any implementation meaning. -/
def H_hist
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :
    Matrix (Index Configuration p) (Index Configuration p) ℚ :=
  L0 p + L1 p modelQ + L2 p

@[simp] theorem H_hist_entry
    {Configuration : Type*} [DecidableEq Configuration]
    (p : Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (output input : Index Configuration p) :
    H_hist p modelQ output input =
      L0 p output input + L1 p modelQ output input + L2 p output input := rfl

end

end HistorySpec
end HistoryBlockEncoding
