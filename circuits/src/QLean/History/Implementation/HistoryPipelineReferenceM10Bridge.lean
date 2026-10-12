import QLean.History.Integration.Checkpoint2
import QLean.Circuits.Foundation.PrimitiveGateProofs
import VerifiedMath.Complexification
import Mathlib
import QLean.SignalProcessing.KernelReflectionQSVTKernelReflection

namespace ExecutableHistoryReferenceM10Bridge

open Matrix
open HistoryBlockEncoding

noncomputable section

def configurationEquiv (Configuration : Type*) [Fintype Configuration] :
    Configuration ≃ Fin (Fintype.card Configuration) :=
  Fintype.equivFin Configuration

def indexEquiv {Configuration : Type*} [Fintype Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters) :
    HistoryBlockEncoding.HistorySpec.Index Configuration p ≃
      JenningsHistory.HistoryIndex (Fintype.card Configuration) p.clockEnd
        p.binaryLabels where
  toFun index :=
    { clock := index.clock
      order := index.state.label
      state := configurationEquiv Configuration index.state.configuration }
  invFun index :=
    { clock := index.clock
      state :=
        { label := index.order
          configuration := (configurationEquiv Configuration).symm index.state } }
  left_inv := by
    intro index
    cases index with
    | mk clock state =>
      cases state with
      | mk label configuration =>
        simp [configurationEquiv]
  right_inv := by
    intro index
    cases index with
    | mk clock order state =>
      simp [configurationEquiv]

def translatedSystem {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (initial : Configuration → ℚ)
    (wf : HistoryBlockEncoding.HistorySpec.WellFormed p) :
    JenningsHistory.HistorySpec (Fintype.card Configuration) p.clockEnd
      p.taylorOrder p.physicalClocks p.binaryLabels where
  step := (p.stepSize : ℝ)
  generator := fun output input =>
    (modelQ ((configurationEquiv Configuration).symm output)
      ((configurationEquiv Configuration).symm input) : ℝ)
  initial := fun state =>
    (initial ((configurationEquiv Configuration).symm state) : ℝ)
  order_lt := wf.2.2.2.1
  physical_pos := wf.1
  physical_lt := wf.2.2.2.2

theorem taylor_condition_iff
    {p : HistoryBlockEncoding.HistorySpec.Parameters}
    (a b : Fin p.binaryLabels) :
    (a.val = b.val + 1 ∧ b.val < p.taylorOrder) ↔
      (a.val > 0 ∧ b.val + 1 = a.val ∧ a.val ≤ p.taylorOrder) := by
  omega

theorem clock_step_condition_iff
    {p : HistoryBlockEncoding.HistorySpec.Parameters}
    {a b : Fin p.clockEnd} {m : Nat}
    (h : a.val = b.val + 1) :
    (b.val < m ↔ a.val ≤ m) := by
  omega

theorem taylor_coefficient_eq
    {Configuration : Type*}
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (a b : Fin p.binaryLabels)
    (output input : Configuration)
    (h : a.val = b.val + 1) :
    ((-(p.stepSize / ((b.val + 1 : Nat) : ℚ)) *
        modelQ output input : ℚ) : ℝ) =
      -(p.stepSize : ℝ) * (modelQ output input : ℝ) / (a.val : ℝ) := by
  rw [h]
  have hpos : 0 < b.val + 1 := by omega
  have hne : ((b.val + 1 : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  push_cast
  field_simp [hne]

theorem successor_condition_iff
    {p : HistoryBlockEncoding.HistorySpec.Parameters}
    (a b : Fin p.binaryLabels) :
    a.val = b.val + 1 ↔
      (a.val > 0 ∧ b.val + 1 = a.val) := by
  omega

theorem taylor_delta_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (initial : Configuration → ℚ)
    (wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (a b : Fin p.binaryLabels)
    (output input : Configuration) :
    JenningsHistory.taylorDeltaEntry (translatedSystem p modelQ initial wf)
        a b (configurationEquiv Configuration output)
          (configurationEquiv Configuration input) =
      (HistoryBlockEncoding.HistorySpec.deltaTay p modelQ
        { label := a, configuration := output }
        { label := b, configuration := input } : ℝ) := by
  by_cases h : a.val = b.val + 1 ∧ b.val < p.taylorOrder
  · have h' := (taylor_condition_iff (p := p) a b).1 h
    rw [JenningsHistory.taylorDeltaEntry, HistoryBlockEncoding.HistorySpec.deltaTay]
    rw [if_pos h, if_pos h']
    simpa [translatedSystem, configurationEquiv] using
      (taylor_coefficient_eq p modelQ a b output input h.1).symm
  · have h' : ¬(a.val > 0 ∧ b.val + 1 = a.val ∧
        a.val ≤ p.taylorOrder) := by
      intro h'
      exact h ((taylor_condition_iff (p := p) a b).2 h')
    rw [JenningsHistory.taylorDeltaEntry, HistoryBlockEncoding.HistorySpec.deltaTay]
    rw [if_neg h, if_neg h']
    norm_num

theorem idle_delta_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (_initial : Configuration → ℚ)
    (_wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (a b : Fin p.binaryLabels)
    (output input : Configuration) :
    JenningsHistory.idleDeltaEntry a b (configurationEquiv Configuration output)
          (configurationEquiv Configuration input) =
      (HistoryBlockEncoding.HistorySpec.deltaIdle p
        { label := a, configuration := output }
        { label := b, configuration := input } : ℝ) := by
  by_cases hsucc : a.val = b.val + 1
  · have hsucc' := (successor_condition_iff (p := p) a b).1 hsucc
    by_cases hconfig : output = input
    · rw [JenningsHistory.idleDeltaEntry, HistoryBlockEncoding.HistorySpec.deltaIdle]
      dsimp
      have hold : a.val = b.val + 1 ∧ output = input := ⟨hsucc, hconfig⟩
      rw [if_pos hsucc']
      simp only [hold]
      simp [JenningsHistory.stateIdentityEntry]
    · have hconfig' :
          configurationEquiv Configuration output ≠
            configurationEquiv Configuration input := by
        intro h
        apply hconfig
        exact (configurationEquiv Configuration).injective h
      rw [JenningsHistory.idleDeltaEntry, HistoryBlockEncoding.HistorySpec.deltaIdle]
      dsimp
      have hold : ¬(a.val = b.val + 1 ∧ output = input) := by
        intro h
        exact hconfig h.2
      rw [if_pos hsucc', if_neg hold]
      simp [JenningsHistory.stateIdentityEntry, hconfig']
  · have hsucc' : ¬(a.val > 0 ∧ b.val + 1 = a.val) := by
      intro h
      exact hsucc ((successor_condition_iff (p := p) a b).2 h)
    rw [JenningsHistory.idleDeltaEntry, HistoryBlockEncoding.HistorySpec.deltaIdle]
    dsimp
    have hold : ¬(a.val = b.val + 1 ∧ output = input) := by
      intro h
      exact hsucc h.1
    rw [if_neg hsucc', if_neg hold]
    norm_num

theorem l1_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (initial : Configuration → ℚ)
    (wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (row col : HistoryBlockEncoding.HistorySpec.Index Configuration p) :
    JenningsHistory.l1Entry (translatedSystem p modelQ initial wf)
        (indexEquiv p row) (indexEquiv p col) =
      (HistoryBlockEncoding.HistorySpec.L1 p modelQ row col : ℝ) := by
  by_cases hclock : row.clock = col.clock
  · have hclock' : (indexEquiv p row).clock = (indexEquiv p col).clock := by
      exact hclock
    unfold JenningsHistory.l1Entry HistoryBlockEncoding.HistorySpec.L1
    by_cases hp : row.clock.val < p.physicalClocks
    · have hphysical' :
          (indexEquiv p row).clock.val < p.physicalClocks := by
        simpa [indexEquiv] using hp
      rw [if_pos hclock', if_pos hclock, if_pos hphysical', if_pos hp]
      change
        JenningsHistory.taylorDeltaEntry (translatedSystem p modelQ initial wf)
            row.state.label col.state.label
            (configurationEquiv Configuration row.state.configuration)
            (configurationEquiv Configuration col.state.configuration) =
          (HistoryBlockEncoding.HistorySpec.deltaTay p modelQ row.state col.state : ℝ)
      exact taylor_delta_entry_eq p modelQ initial wf
        row.state.label col.state.label row.state.configuration
          col.state.configuration
    · have hphysical' :
          ¬(indexEquiv p row).clock.val < p.physicalClocks := by
        simpa [indexEquiv] using hp
      rw [if_pos hclock', if_pos hclock, if_neg hphysical', if_neg hp]
      change
        JenningsHistory.idleDeltaEntry row.state.label col.state.label
            (configurationEquiv Configuration row.state.configuration)
            (configurationEquiv Configuration col.state.configuration) =
          (HistoryBlockEncoding.HistorySpec.deltaIdle p row.state col.state : ℝ)
      exact idle_delta_entry_eq p initial wf
        row.state.label col.state.label row.state.configuration
          col.state.configuration
  · have hclock' : ¬(indexEquiv p row).clock = (indexEquiv p col).clock := by
      intro h
      apply hclock
      exact h
    unfold JenningsHistory.l1Entry HistoryBlockEncoding.HistorySpec.L1
    rw [if_neg hclock', if_neg hclock]
    norm_num

theorem sigma_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (a b : Fin p.binaryLabels)
    (output input : Configuration) :
    (if a.val = 0 ∧ b.val ≤ p.taylorOrder ∧
          configurationEquiv Configuration output =
            configurationEquiv Configuration input then
        (-1 : ℝ) else 0) =
      ((-(HistoryBlockEncoding.HistorySpec.fSigma p
        { label := a, configuration := output }
        { label := b, configuration := input }) : ℚ) : ℝ) := by
  by_cases ha : a.val = 0
  · by_cases hb : b.val ≤ p.taylorOrder
    · by_cases hc : output = input
      · have hc' : configurationEquiv Configuration output =
            configurationEquiv Configuration input := by
          exact congrArg (configurationEquiv Configuration) hc
        simp [HistoryBlockEncoding.HistorySpec.fSigma, ha, hb, hc]
      · have hc' : configurationEquiv Configuration output ≠
            configurationEquiv Configuration input := by
          intro h
          apply hc
          exact (configurationEquiv Configuration).injective h
        simp [HistoryBlockEncoding.HistorySpec.fSigma, ha, hb, hc, hc']
    · simp [HistoryBlockEncoding.HistorySpec.fSigma, ha, hb]
  · simp [HistoryBlockEncoding.HistorySpec.fSigma, ha]

theorem bin_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (a b : Fin p.binaryLabels)
    (output input : Configuration) :
    (if a.val = 0 ∧ b.val + 1 = p.binaryLabels ∧
          configurationEquiv Configuration output =
            configurationEquiv Configuration input then
        (-1 : ℝ) else 0) =
      ((-(HistoryBlockEncoding.HistorySpec.fBin p
        { label := a, configuration := output }
        { label := b, configuration := input }) : ℚ) : ℝ) := by
  by_cases ha : a.val = 0
  · by_cases hb : b.val + 1 = p.binaryLabels
    · by_cases hc : output = input
      · have hc' : configurationEquiv Configuration output =
            configurationEquiv Configuration input := by
          exact congrArg (configurationEquiv Configuration) hc
        simp [HistoryBlockEncoding.HistorySpec.fBin, ha, hb, hc]
      · have hc' : configurationEquiv Configuration output ≠
            configurationEquiv Configuration input := by
          intro h
          apply hc
          exact (configurationEquiv Configuration).injective h
        simp [HistoryBlockEncoding.HistorySpec.fBin, ha, hb, hc, hc']
    · simp [HistoryBlockEncoding.HistorySpec.fBin, ha, hb]
  · simp [HistoryBlockEncoding.HistorySpec.fBin, ha]

theorem l2_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (_modelQ : Matrix Configuration Configuration ℚ)
    (_initial : Configuration → ℚ)
    (_wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (row col : HistoryBlockEncoding.HistorySpec.Index Configuration p) :
    JenningsHistory.l2Entry (translatedSystem p _modelQ _initial _wf)
        (indexEquiv p row) (indexEquiv p col) =
      (HistoryBlockEncoding.HistorySpec.L2 p row col : ℝ) := by
  unfold JenningsHistory.l2Entry HistoryBlockEncoding.HistorySpec.L2
  by_cases hstep : row.clock.val = col.clock.val + 1
  · have hstep' :
        (indexEquiv p row).clock.val = (indexEquiv p col).clock.val + 1 := by
      simpa [indexEquiv] using hstep
    rw [if_pos hstep', if_pos hstep]
    by_cases hphysical : col.clock.val < p.physicalClocks
    · have hphysical' :
          (indexEquiv p row).clock.val ≤ p.physicalClocks := by
        have hrow : row.clock.val ≤ p.physicalClocks :=
          (clock_step_condition_iff
            (a := row.clock) (b := col.clock) hstep).1 hphysical
        simpa [indexEquiv] using hrow
      rw [if_pos hphysical', if_pos hphysical]
      change
        (if row.state.label.val = 0 ∧
              col.state.label.val ≤ p.taylorOrder ∧
              (configurationEquiv Configuration row.state.configuration) =
                (configurationEquiv Configuration col.state.configuration) then
            (-1 : ℝ) else 0) =
          ((-(HistoryBlockEncoding.HistorySpec.fSigma p row.state col.state) : ℚ) : ℝ)
      exact sigma_entry_eq p row.state.label col.state.label
        row.state.configuration col.state.configuration
    · have hphysical' :
          ¬((indexEquiv p row).clock.val ≤ p.physicalClocks) := by
        intro h
        apply hphysical
        exact (clock_step_condition_iff
          (a := row.clock) (b := col.clock) hstep).2 (by
            simpa [indexEquiv] using h)
      rw [if_neg hphysical', if_neg hphysical]
      change
        (if row.state.label.val = 0 ∧
              col.state.label.val + 1 = p.binaryLabels ∧
              (configurationEquiv Configuration row.state.configuration) =
                (configurationEquiv Configuration col.state.configuration) then
            (-1 : ℝ) else 0) =
          ((-(HistoryBlockEncoding.HistorySpec.fBin p row.state col.state) : ℚ) : ℝ)
      exact bin_entry_eq p row.state.label col.state.label
        row.state.configuration col.state.configuration
  · have hstep' :
        ¬((indexEquiv p row).clock.val = (indexEquiv p col).clock.val + 1) := by
      intro h
      apply hstep
      simpa [indexEquiv] using h
    rw [if_neg hstep', if_neg hstep]
    norm_num

theorem l0_entry_eq
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (_modelQ : Matrix Configuration Configuration ℚ)
    (_initial : Configuration → ℚ)
    (_wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (row col : HistoryBlockEncoding.HistorySpec.Index Configuration p) :
    JenningsHistory.l0Entry (indexEquiv p row) (indexEquiv p col) =
      (HistoryBlockEncoding.HistorySpec.L0 p row col : ℝ) := by
  have hiff :
      (row.clock = col.clock ∧ row.state.label = col.state.label ∧
        row.state.configuration = col.state.configuration) ↔ row = col := by
    constructor
    · intro h
      cases row with
      | mk rowClock rowState =>
        cases rowState with
        | mk rowLabel rowConfiguration =>
          cases col with
          | mk colClock colState =>
            cases colState with
            | mk colLabel colConfiguration =>
              simp_all
    · intro h
      subst col
      simp
  by_cases h : row = col <;>
    simp [JenningsHistory.l0Entry, HistoryBlockEncoding.HistorySpec.L0, indexEquiv,
      configurationEquiv, hiff, h]

theorem history_matrix_entry_eq_cast_h_hist
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (initial : Configuration → ℚ)
    (wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (row col : HistoryBlockEncoding.HistorySpec.Index Configuration p) :
    JenningsHistory.historyMatrix (translatedSystem p modelQ initial wf)
        (indexEquiv p row) (indexEquiv p col) =
      (HistoryBlockEncoding.Checkpoint2.RealHistory.castMatrix
        (HistoryBlockEncoding.HistorySpec.H_hist p modelQ) row col) := by
  change
    JenningsHistory.l0Entry (indexEquiv p row) (indexEquiv p col) +
        JenningsHistory.l1Entry (translatedSystem p modelQ initial wf)
          (indexEquiv p row) (indexEquiv p col) +
        JenningsHistory.l2Entry (translatedSystem p modelQ initial wf)
          (indexEquiv p row) (indexEquiv p col) =
      ((HistoryBlockEncoding.HistorySpec.L0 p row col +
          HistoryBlockEncoding.HistorySpec.L1 p modelQ row col +
          HistoryBlockEncoding.HistorySpec.L2 p row col : ℚ) : ℝ)
  rw [l0_entry_eq p modelQ initial wf row col,
    l1_entry_eq p modelQ initial wf row col,
    l2_entry_eq p modelQ initial wf row col]
  norm_num

end
end ExecutableHistoryReferenceM10Bridge
