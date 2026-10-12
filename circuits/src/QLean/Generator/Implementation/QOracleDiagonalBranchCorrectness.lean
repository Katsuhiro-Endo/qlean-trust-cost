import QLean.Generator.Implementation.QOracleEndToEnd
import QLean.Generator.Implementation.ReversibleLocality
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# Q oracle 対角分岐の一般基底作用

column/row oracle の `6i`・`6i+1` 分岐について、任意の `q,K`、slot、copy で、
selector 判定、persistent flag、出力 XOR、compute--use--uncompute による一時領域の
復元を計算基底作用だけから証明する。巨大行列や全基底の列挙は用いない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- oracle work slice 全体の wire 列。 -/
def diagonalOracleWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  ((QLayout.canonical p).oracleWork.wireList :
    List (Wire p.ancillaWidth p.systemWidth))

/-- column 対角分岐の compute が参照する局所 support。 -/
def columnDiagonalComputeSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  columnSelectorWires p ++ diagonalOracleWorkWires p

/-- row 対角分岐の compute が参照する局所 support。 -/
def rowDiagonalComputeSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  rowSelectorWires p ++ diagonalOracleWorkWires p

/-- selector と定数の little-endian bit 列が一致するかを表す純粋な条件。 -/
def diagonalSelectorMatches
    {ancillaQubits systemQubits : Nat}
    (selector : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (input : JointBasis ancillaQubits systemQubits) : Bool :=
  decide (readWires selector input = constantBits constant selector.length)

/-- 対角分岐の selector 比較と三正制御 AND を合成した compute 回路。 -/
def xorSelectorMatchIntoBranchFlagCircuit (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (constant : Nat) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq
    (selectorEqualsConstant selector (decoderAndScratchWires p) constant
      (oracleSelectedWire p))
    (positiveMultiControlledX
      [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot]
      (decoderAndScratchWires p) (oracleBranchWire p))

/-- compute 回路の、行列を使わない純粋な基底作用。 -/
def selectorMatchBranchFlagXorReference (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (constant : Nat)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let selected :=
    if diagonalSelectorMatches selector constant input then
      xBasisAction (oracleSelectedWire p) input
    else input
  if allWiresTrue
      [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot]
      selected then
    xBasisAction (oracleBranchWire p) selected
  else selected

/-- 対角分岐で要求する clean な一時領域と persistent flag 値。 -/
structure DiagonalBranchCleanInput (p : QParameters) (slot : Fin p.K)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- decoder の多重 AND scratch はすべて 0 である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- selector 比較結果の一時 bit は 0 である。 -/
  selected_zero : input (oracleSelectedWire p) = false
  /-- 分岐 AND の一時 bit は 0 である。 -/
  branch_zero : input (oracleBranchWire p) = false
  /-- compact decoder が保持する合法性 bit は指定値である。 -/
  legal_value : input (oracleLegalWire p) = legalValue
  /-- compact decoder が保持する slot の present bit は指定値である。 -/
  present_value : input (oraclePresentWireAt p slot) = presentValue

/-- selector 一致、legal、present の論理積として定義した分岐有効条件。 -/
def diagonalBranchEnabled (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (_slot : Fin p.K) (constant : Nat) (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  diagonalSelectorMatches selector constant input && legalValue && presentValue

/-- 三正制御 AND は canonical scratch 本数で実装できる。 -/
theorem diagonalBranch_three_le_scratch_add_one (p : QParameters) :
    3 ≤ (decoderAndScratchWires p).length + 1 := by
  have scratchEnough := decoderAndScratchWires_wordWidth_le p
  have wordLower : 2 ≤ p.wordWidth := by
    have positive := p.q_pos
    simp [QParameters.wordWidth]
    omega
  omega

/-- canonical oracle layout では legal・selected・present・scratch・branch は重複しない。 -/
theorem diagonalBranch_controls_scratch_branch_nodup
    (p : QParameters) (slot : Fin p.K) :
    ([oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot] ++
      decoderAndScratchWires p ++ [oracleBranchWire p]).Nodup := by
  let legal := QLayout.oracleSlice (OracleWorkLayout.canonical p).legal
  let selected := QLayout.oracleSlice (OracleWorkLayout.canonical p).selected
  let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  let branch := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  let andWork := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have prefixBeforeScratch : branch.start + 1 ≤ andWork.start := by
    simp [branch, andWork, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have controlsNodup :
      [oracleLegalWire p, oracleSelectedWire p,
        oraclePresentWireAt p slot, oracleBranchWire p].Nodup := by
    have legalNeSelected : oracleLegalWire p ≠ oracleSelectedWire p := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, oracleSelectedWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
      omega
    have legalNePresent : oracleLegalWire p ≠ oraclePresentWireAt p slot := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, oraclePresentWireAt, QLayout.oracleSlice,
        RegisterSlice.compose, OracleWorkLayout.canonical, wireNumber,
        RegisterSlice.ancillaWire, RegisterSlice.index,
        QParameters.presentWidth] at numbers
      omega
    have legalNeBranch : oracleLegalWire p ≠ oracleBranchWire p := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, oracleBranchWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
      omega
    have selectedNePresent :
        oracleSelectedWire p ≠ oraclePresentWireAt p slot := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleSelectedWire, oraclePresentWireAt, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
        QParameters.presentWidth] at numbers
      omega
    have selectedNeBranch : oracleSelectedWire p ≠ oracleBranchWire p := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleSelectedWire, oracleBranchWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
      omega
    have presentNeBranch : oraclePresentWireAt p slot ≠ oracleBranchWire p := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oraclePresentWireAt, oracleBranchWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
        QParameters.presentWidth] at numbers
      omega
    simp [legalNeSelected, legalNePresent, legalNeBranch, selectedNePresent,
      selectedNeBranch, presentNeBranch]
  have scratchNodup : (decoderAndScratchWires p).Nodup := by
    have full :
        (andWork.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup :=
      andWork.wireList_nodup
    have dropped :
        ((andWork.wireList : List (Wire p.ancillaWidth p.systemWidth)).drop
          (3 * (p.K - 1) + 2)).Nodup := full.drop
    simpa [decoderAndScratchWires, oracleAndWorkWires, andWork,
      RegisterSlice.wireList] using dropped
  have controlsDisjointScratch :
      [oracleLegalWire p, oracleSelectedWire p,
        oraclePresentWireAt p slot, oracleBranchWire p].Disjoint
        (decoderAndScratchWires p) := by
    rw [List.disjoint_left]
    intro wire controlMember scratchMember
    have scratchInAnd : wire ∈
        (andWork.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [decoderAndScratchWires, oracleAndWorkWires, andWork,
        RegisterSlice.wireList] using List.mem_of_mem_drop scratchMember
    have branchAndDisjoint :
        (branch.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (andWork.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      branch.wireList_disjoint_of_end_le_start andWork prefixBeforeScratch
    have legalMember : oracleLegalWire p ∈
        (legal.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      change legal.ancillaWire 0 ∈
        (legal.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
    have selectedMember : oracleSelectedWire p ∈
        (selected.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      change selected.ancillaWire 0 ∈
        (selected.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
    have presentMember : oraclePresentWireAt p slot ∈
        (present.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      change present.ancillaWire slot ∈
        (present.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
    have branchMember : oracleBranchWire p ∈
        (branch.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      change branch.ancillaWire 0 ∈
        (branch.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at controlMember
    rcases controlMember with controlEq | controlEq | controlEq | controlEq
    · have before : legal.start + 1 ≤ andWork.start := by
        simp [legal, andWork, QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]
        omega
      exact (List.disjoint_left.mp
        (legal.wireList_disjoint_of_end_le_start andWork before))
        legalMember (controlEq ▸ scratchInAnd)
    · have before : selected.start + 1 ≤ andWork.start := by
        simp [selected, andWork, QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]
        omega
      exact (List.disjoint_left.mp
        (selected.wireList_disjoint_of_end_le_start andWork before))
        selectedMember (controlEq ▸ scratchInAnd)
    · have before : present.start + p.presentWidth ≤ andWork.start := by
        simp [present, andWork, QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]
        omega
      exact (List.disjoint_left.mp
        (present.wireList_disjoint_of_end_le_start andWork before))
        presentMember (controlEq ▸ scratchInAnd)
    · exact (List.disjoint_left.mp branchAndDisjoint)
        branchMember (controlEq ▸ scratchInAnd)
  have branchAbsentScratch : oracleBranchWire p ∉ decoderAndScratchWires p := by
    intro member
    exact (List.disjoint_left.mp controlsDisjointScratch)
      (by simp) member
  have controlsWithoutBranchNodup :
      [oracleLegalWire p, oracleSelectedWire p,
        oraclePresentWireAt p slot].Nodup := by
    have taken :
        ([oracleLegalWire p, oracleSelectedWire p,
          oraclePresentWireAt p slot, oracleBranchWire p].take 3).Nodup :=
      controlsNodup.take
    simpa using taken
  apply List.nodup_append.mpr
  refine ⟨?_, by simp, ?_⟩
  · exact List.nodup_append.mpr
      ⟨controlsWithoutBranchNodup, scratchNodup, by
        intro left leftMember right rightMember equal
        have leftInFour : left ∈
            [oracleLegalWire p, oracleSelectedWire p,
              oraclePresentWireAt p slot, oracleBranchWire p] := by
          simp only [List.mem_cons] at leftMember ⊢
          tauto
        exact (List.disjoint_left.mp controlsDisjointScratch)
          leftInFour (equal ▸ rightMember)⟩
  · intro wire member target targetMember
    have targetEq : target = oracleBranchWire p := by simpa using targetMember
    subst target
    intro equal
    subst wire
    rcases List.mem_append.mp member with controlMember | scratchMember
    · have combined :
          ([oracleLegalWire p, oracleSelectedWire p,
            oraclePresentWireAt p slot] ++ [oracleBranchWire p]).Nodup := by
        simpa using controlsNodup
      have separated := (List.nodup_append.mp combined).2.2
      have branchAbsent : oracleBranchWire p ∉
          [oracleLegalWire p, oracleSelectedWire p,
            oraclePresentWireAt p slot] := by
        intro branchMember
        exact separated (oracleBranchWire p) branchMember
          (oracleBranchWire p) (by simp) rfl
      exact branchAbsent controlMember
    · exact branchAbsentScratch scratchMember

/-- selector 比較後も、分岐 AND が使う scratch は 0 のまま保存される。 -/
theorem diagonalSelectorState_scratch_zero
    (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (constant : Nat) (input : JointBasis p.ancillaWidth p.systemWidth)
    (selectorLayout :
      (selector ++ decoderAndScratchWires p ++ [oracleSelectedWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false) :
    let selected :=
      if diagonalSelectorMatches selector constant input then
        xBasisAction (oracleSelectedWire p) input
      else input
    ∀ wire ∈ decoderAndScratchWires p, selected wire = false := by
  dsimp only
  intro wire member
  have selectedAbsent : oracleSelectedWire p ∉ decoderAndScratchWires p := by
    have prefixNodup := (List.nodup_append.mp selectorLayout).1
    have separated := (List.nodup_append.mp selectorLayout).2.2
    intro selectedMember
    exact separated (oracleSelectedWire p)
      (List.mem_append_right selector selectedMember)
      (oracleSelectedWire p) (by simp) rfl
  have wireDifferent : wire ≠ oracleSelectedWire p := by
    intro equal
    subst wire
    exact selectedAbsent member
  by_cases isMatch : diagonalSelectorMatches selector constant input = true
  · simp [isMatch, xBasisAction_other (oracleSelectedWire p) wire wireDifferent,
      scratchZero wire member]
  · have disabled := Bool.eq_false_of_not_eq_true isMatch
    simp [disabled, scratchZero wire member]

/-- clean 入力上の対角 compute 回路は純粋な基底作用と一致する。 -/
theorem runBasis_xorSelectorMatchIntoBranchFlagCircuit
    (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (constant : Nat)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (selectorLength : selector.length = p.selectorWidth)
    (selectorLayout :
      (selector ++ decoderAndScratchWires p ++ [oracleSelectedWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false) :
    (xorSelectorMatchIntoBranchFlagCircuit p selector slot constant).runBasis
        reversibleGatePermutation input =
      selectorMatchBranchFlagXorReference p selector slot constant input := by
  let selected :=
    if diagonalSelectorMatches selector constant input then
      xBasisAction (oracleSelectedWire p) input
    else input
  have selectorRun :
      (selectorEqualsConstant selector (decoderAndScratchWires p) constant
        (oracleSelectedWire p)).runBasis reversibleGatePermutation input = selected := by
    have result := runBasis_selectorEqualsConstant_bits selector
      (decoderAndScratchWires p) constant (oracleSelectedWire p) input
      (by simpa [selectorLength] using selectorWidth_le_decoderAndScratch_add_one p)
      selectorLayout scratchZero
    simpa [selected, diagonalSelectorMatches] using result
  have scratchStillZero :
      ∀ wire ∈ decoderAndScratchWires p, selected wire = false :=
    diagonalSelectorState_scratch_zero p selector constant input selectorLayout
      scratchZero
  rw [xorSelectorMatchIntoBranchFlagCircuit, runBasis_seq, selectorRun]
  rw [runBasis_positiveMultiControlledX
    [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot]
    (decoderAndScratchWires p) (oracleBranchWire p) selected
    (diagonalBranch_three_le_scratch_add_one p)
    (diagonalBranch_controls_scratch_branch_nodup p slot) scratchStillZero]
  rfl

/-- clean 入力では compute 後の branch bit が selector・legal・present の積に等しい。 -/
theorem selectorMatchBranchFlagXorReference_branch
    (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (constant : Nat) (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    selectorMatchBranchFlagXorReference p selector slot constant input
        (oracleBranchWire p) =
      diagonalBranchEnabled p selector slot constant legalValue presentValue input := by
  have layout := diagonalBranch_controls_scratch_branch_nodup p slot
  have legalFresh := (List.nodup_cons.mp layout).1
  have afterLegal := (List.nodup_cons.mp layout).2
  have selectedFresh := (List.nodup_cons.mp afterLegal).1
  have afterSelected := (List.nodup_cons.mp afterLegal).2
  have presentFresh := (List.nodup_cons.mp afterSelected).1
  have legalNeSelected : oracleLegalWire p ≠ oracleSelectedWire p := by
    intro equal
    exact legalFresh (by simp [equal])
  have legalNeBranch : oracleLegalWire p ≠ oracleBranchWire p := by
    intro equal
    exact legalFresh (by simp [equal])
  have selectedNePresent :
      oracleSelectedWire p ≠ oraclePresentWireAt p slot := by
    intro equal
    exact selectedFresh (by simp [equal])
  have selectedNeBranch : oracleSelectedWire p ≠ oracleBranchWire p := by
    intro equal
    exact selectedFresh (by simp [equal])
  have presentNeBranch : oraclePresentWireAt p slot ≠ oracleBranchWire p := by
    intro equal
    exact presentFresh (by simp [equal])
  have branchNeSelected : oracleBranchWire p ≠ oracleSelectedWire p :=
    selectedNeBranch.symm
  have branchNeLegal : oracleBranchWire p ≠ oracleLegalWire p := legalNeBranch.symm
  have branchNePresent : oracleBranchWire p ≠ oraclePresentWireAt p slot :=
    presentNeBranch.symm
  have legalNeBranch' := legalNeBranch
  have presentNeSelected := selectedNePresent.symm
  have selectedZero := clean.selected_zero
  have branchZero := clean.branch_zero
  have legalRead := clean.legal_value
  have presentRead := clean.present_value
  by_cases isMatch : diagonalSelectorMatches selector constant input = true <;>
    cases legalValue <;> cases presentValue <;>
    simp_all [selectorMatchBranchFlagXorReference, diagonalBranchEnabled, allWiresTrue,
      readWires, xBasisAction]

/-- column selector を用いる compute 回路の一般基底作用。 -/
theorem runBasis_columnDiagonalCompute
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false) :
    (xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
        (6 * slot.val + copy.val)).runBasis reversibleGatePermutation input =
      selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) input := by
  exact runBasis_xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
    (6 * slot.val + copy.val) input (by simp [columnSelectorWires])
    (columnSelector_decoderScratch_selected_nodup p) scratchZero

/-- row selector を用いる compute 回路の一般基底作用。 -/
theorem runBasis_rowDiagonalCompute
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false) :
    (xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
        (6 * slot.val + copy.val)).runBasis reversibleGatePermutation input =
      selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) input := by
  exact runBasis_xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
    (6 * slot.val + copy.val) input (by simp [rowSelectorWires])
    (rowSelector_decoderScratch_selected_nodup p) scratchZero

/-- column 対角分岐の use 部分。 -/
def controlledXorColumnDiagonalResultIntoOutputsCircuit (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let selectorValue := 6 * slot.val + copy.val
  .seq (controlledXorCopy (oracleBranchWire p)
      (columnKeyWires p) (rowOutputWires p)) <|
    .seq (controlledXorConstant (oracleBranchWire p)
      (selectorOutputWires p) selectorValue) <|
    .seq (safeCnot (oracleBranchWire p) (negativeWire p)) <|
    safeCnot (oracleBranchWire p) (activeWire p)

/-- row 対角分岐の use 部分。 -/
def controlledXorRowDiagonalResultIntoOutputsCircuit (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let selectorValue := 6 * slot.val + copy.val
  .seq (controlledXorCopy (oracleBranchWire p)
      (systemWires p) (columnKeyWires p)) <|
    .seq (controlledXorConstant (oracleBranchWire p)
      (columnSelectorWires p) selectorValue) <|
    safeCnot (oracleBranchWire p) (keySignalWire p)

/-- column 対角分岐の正本 AST は、明示した compute と use の C-U-U 合成である。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_eq_computeUseUncompute
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    columnDiagonalResultComputeUseUncomputeCircuit p slot copy =
      Circuit.computeUseUncompute id
        (xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
          (6 * slot.val + copy.val))
        (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy) := by
  rfl

/-- row 対角分岐の正本 AST は、明示した compute と use の C-U-U 合成である。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_eq_computeUseUncompute
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    rowDiagonalResultComputeUseUncomputeCircuit p slot copy =
      Circuit.computeUseUncompute id
        (xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
          (6 * slot.val + copy.val))
        (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy) := by
  rfl

/-- oracle 内部 slice の wire は最上位 oracle work slice 全体にも属する。 -/
theorem diagonalOracleSlice_subset_work
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width) :
    ∀ {wire : Wire p.ancillaWidth p.systemWidth},
      wire ∈ (QLayout.oracleSlice slice).wireList →
        wire ∈ diagonalOracleWorkWires p := by
  intro wire member
  exact RegisterSlice.compose_wireList_subset
    (QLayout.canonical p).oracleWork slice member

/-- branch 一時 bit は oracle work slice 全体に属する。 -/
theorem oracleBranchWire_mem_diagonalOracleWorkWires (p : QParameters) :
    oracleBranchWire p ∈ diagonalOracleWorkWires p := by
  let branch := (OracleWorkLayout.canonical p).branch
  apply diagonalOracleSlice_subset_work p branch
  change (QLayout.oracleSlice branch).ancillaWire 0 ∈
    ((QLayout.oracleSlice branch).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- selected 一時 bit は oracle work slice 全体に属する。 -/
theorem oracleSelectedWire_mem_diagonalOracleWorkWires (p : QParameters) :
    oracleSelectedWire p ∈ diagonalOracleWorkWires p := by
  let selected := (OracleWorkLayout.canonical p).selected
  apply diagonalOracleSlice_subset_work p selected
  change (QLayout.oracleSlice selected).ancillaWire 0 ∈
    ((QLayout.oracleSlice selected).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- legal persistent bit は oracle work slice 全体に属する。 -/
theorem oracleLegalWire_mem_diagonalOracleWorkWires (p : QParameters) :
    oracleLegalWire p ∈ diagonalOracleWorkWires p := by
  let legal := (OracleWorkLayout.canonical p).legal
  apply diagonalOracleSlice_subset_work p legal
  change (QLayout.oracleSlice legal).ancillaWire 0 ∈
    ((QLayout.oracleSlice legal).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- 任意 slot の present persistent bit は oracle work slice 全体に属する。 -/
theorem oraclePresentWireAt_mem_diagonalOracleWorkWires
    (p : QParameters) (slot : Fin p.K) :
    oraclePresentWireAt p slot ∈ diagonalOracleWorkWires p := by
  let present := (OracleWorkLayout.canonical p).present
  apply diagonalOracleSlice_subset_work p present
  change (QLayout.oracleSlice present).ancillaWire slot ∈
    ((QLayout.oracleSlice present).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩

/-- decoder AND scratch の各 wire は oracle work slice 全体に属する。 -/
theorem decoderAndScratchWire_mem_diagonalOracleWorkWires
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ decoderAndScratchWires p) :
    wire ∈ diagonalOracleWorkWires p := by
  let andWork := (OracleWorkLayout.canonical p).andWork
  apply diagonalOracleSlice_subset_work p andWork
  have fullMember : wire ∈ oracleAndWorkWires p := List.mem_of_mem_drop member
  simpa [oracleAndWorkWires, andWork, RegisterSlice.wireList] using fullMember

/-- selector slice と oracle work に挟まれた最上位 slice は compute support と交わらない。 -/
theorem selectorOracleSupport_disjoint_slice
    (p : QParameters) {selectorWidth targetWidth : Nat}
    (selector : RegisterSlice p.ancillaWidth selectorWidth)
    (target : RegisterSlice p.ancillaWidth targetWidth)
    (selectorBefore : selector.start + selectorWidth ≤ target.start)
    (targetBeforeWork : target.start + targetWidth ≤
      (QLayout.canonical p).oracleWork.start) :
    ((selector.wireList : List (Wire p.ancillaWidth p.systemWidth)) ++
      diagonalOracleWorkWires p).Disjoint
        (target.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
  have selectorDisjoint :
      (selector.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (target.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    selector.wireList_disjoint_of_end_le_start target selectorBefore
  have targetWorkDisjoint :
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    target.wireList_disjoint_of_end_le_start
      (QLayout.canonical p).oracleWork targetBeforeWork
  rw [List.disjoint_left]
  intro wire supportMember targetMember
  rcases List.mem_append.mp supportMember with selectorMember | workMember
  · exact (List.disjoint_left.mp selectorDisjoint) selectorMember targetMember
  · exact (List.disjoint_left.mp targetWorkDisjoint) targetMember workMember

/-- column compute support は row-output register と交わらない。 -/
theorem columnDiagonalSupport_disjoint_rowOutput (p : QParameters) :
    (columnDiagonalComputeSupport p).Disjoint (rowOutputWires p) := by
  let selector := (QLayout.canonical p).columnSelector
  let target := (QLayout.canonical p).rowOutput
  have disjoint := selectorOracleSupport_disjoint_slice p selector target
    (by simp [selector, target, QLayout.canonical]; omega)
    (by simp [target, QLayout.canonical]; omega)
  simpa [columnDiagonalComputeSupport, columnSelectorWires,
    columnSelectorWire, rowOutputWires, rowOutputWire,
    diagonalOracleWorkWires, selector, target, RegisterSlice.wireList] using disjoint

/-- column compute support は selector-output register と交わらない。 -/
theorem columnDiagonalSupport_disjoint_selectorOutput (p : QParameters) :
    (columnDiagonalComputeSupport p).Disjoint (selectorOutputWires p) := by
  let selector := (QLayout.canonical p).columnSelector
  let target := (QLayout.canonical p).selectorOutput
  have disjoint := selectorOracleSupport_disjoint_slice p selector target
    (by simp [selector, target, QLayout.canonical]; omega)
    (by simp [target, QLayout.canonical]; omega)
  simpa [columnDiagonalComputeSupport, columnSelectorWires,
    columnSelectorWire, selectorOutputWires, selectorOutputWire,
    diagonalOracleWorkWires, selector, target, RegisterSlice.wireList] using disjoint

/-- column compute support は negative bit を含まない。 -/
theorem negativeWire_not_mem_columnDiagonalSupport (p : QParameters) :
    negativeWire p ∉ columnDiagonalComputeSupport p := by
  let selector := (QLayout.canonical p).columnSelector
  let target := (QLayout.canonical p).negative
  have disjoint := selectorOracleSupport_disjoint_slice p selector target
    (by simp [selector, target, QLayout.canonical]; omega)
    (by simp [target, QLayout.canonical])
  have targetMember : negativeWire p ∈
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change target.ancillaWire 0 ∈
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  intro member
  apply (List.disjoint_left.mp disjoint)
    (by simpa [columnDiagonalComputeSupport, columnSelectorWires,
      columnSelectorWire, diagonalOracleWorkWires, selector,
      RegisterSlice.wireList] using member)
    targetMember

/-- column compute support は active bit を含まない。 -/
theorem activeWire_not_mem_columnDiagonalSupport (p : QParameters) :
    activeWire p ∉ columnDiagonalComputeSupport p := by
  let selector := (QLayout.canonical p).columnSelector
  let target := (QLayout.canonical p).active
  have disjoint := selectorOracleSupport_disjoint_slice p selector target
    (by simp [selector, target, QLayout.canonical]; omega)
    (by simp [target, QLayout.canonical])
  have targetMember : activeWire p ∈
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change target.ancillaWire 0 ∈
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  intro member
  apply (List.disjoint_left.mp disjoint)
    (by simpa [columnDiagonalComputeSupport, columnSelectorWires,
      columnSelectorWire, diagonalOracleWorkWires, selector,
      RegisterSlice.wireList] using member)
    targetMember

/-- row compute support は column-key register と交わらない。 -/
theorem rowDiagonalSupport_disjoint_columnKey (p : QParameters) :
    (rowDiagonalComputeSupport p).Disjoint (columnKeyWires p) := by
  let selector := (QLayout.canonical p).rowSelector
  let target := (QLayout.canonical p).columnKey
  have targetSelectorDisjoint :
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (selector.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    target.wireList_disjoint_of_end_le_start selector
      (by simp [selector, target, QLayout.canonical])
  have targetWorkDisjoint :
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    target.wireList_disjoint_of_end_le_start
      (QLayout.canonical p).oracleWork
      (by simp [target, QLayout.canonical]; omega)
  rw [List.disjoint_left]
  intro wire supportMember targetMember
  rcases List.mem_append.mp supportMember with selectorMember | workMember
  · exact (List.disjoint_left.mp targetSelectorDisjoint) targetMember
      (by simpa [rowDiagonalComputeSupport, rowSelectorWires, rowSelectorWire,
        selector, RegisterSlice.wireList] using selectorMember)
  · exact (List.disjoint_left.mp targetWorkDisjoint) targetMember workMember

/-- row compute support は column-selector register と交わらない。 -/
theorem rowDiagonalSupport_disjoint_columnSelector (p : QParameters) :
    (rowDiagonalComputeSupport p).Disjoint (columnSelectorWires p) := by
  let selector := (QLayout.canonical p).rowSelector
  let target := (QLayout.canonical p).columnSelector
  have disjoint := selectorOracleSupport_disjoint_slice p selector target
    (by simp [selector, target, QLayout.canonical])
    (by simp [target, QLayout.canonical]; omega)
  simpa [rowDiagonalComputeSupport, rowSelectorWires, rowSelectorWire,
    columnSelectorWires, columnSelectorWire, diagonalOracleWorkWires,
    selector, target, RegisterSlice.wireList] using disjoint

/-- row compute support は key-signal bit を含まない。 -/
theorem keySignalWire_not_mem_rowDiagonalSupport (p : QParameters) :
    keySignalWire p ∉ rowDiagonalComputeSupport p := by
  let selector := (QLayout.canonical p).rowSelector
  let target := (QLayout.canonical p).keySignal
  have disjoint := selectorOracleSupport_disjoint_slice p selector target
    (by simp [selector, target, QLayout.canonical]; omega)
    (by simp [target, QLayout.canonical]; omega)
  have targetMember : keySignalWire p ∈
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change target.ancillaWire 0 ∈
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  intro member
  apply (List.disjoint_left.mp disjoint)
    (by simpa [rowDiagonalComputeSupport, rowSelectorWires, rowSelectorWire,
      diagonalOracleWorkWires, selector, RegisterSlice.wireList] using member)
    targetMember

/-- controlled 定数 XOR は target 外の wire を保存する。 -/
theorem runBasis_controlledXorConstant_outside
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (targets : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (controlAbsent : control ∉ targets)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ targets) :
    (controlledXorConstant control targets constant).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_controlledXorConstant control targets constant input controlAbsent]
  exact controlledXorConstantBasisAction_outside control constant 0 targets input
    wire outside

/-- safe CNOT は target 以外の wire を保存する。 -/
theorem runBasis_safeCnot_outside
    {ancillaQubits systemQubits : Nat}
    (control target wire : Wire ancillaQubits systemQubits)
    (controlDifferent : control ≠ target) (wireDifferent : wire ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    (safeCnot control target).runBasis reversibleGatePermutation input wire =
      input wire := by
  rw [runBasis_safeCnot control target controlDifferent]
  exact cnotBasisAction_other control target wire wireDifferent input

/-- 対角 compute は selector と oracle work からなる support だけを参照する。 -/
theorem xorSelectorMatchIntoBranchFlagCircuit_usesOnly
    (p : QParameters)
    (selector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (constant : Nat) :
    circuitUsesOnly (selector ++ diagonalOracleWorkWires p)
      (xorSelectorMatchIntoBranchFlagCircuit p selector slot constant) := by
  constructor
  · change circuitUsesOnly (selector ++ diagonalOracleWorkWires p)
      (boolMultiControlledX (selectorConstantControls selector constant)
        (decoderAndScratchWires p) (oracleSelectedWire p))
    apply circuitUsesOnly_boolMultiControlledX
    · intro control controlMember
      have wireMember : control.1 ∈ selector := by
        have mapped : control.1 ∈
            (selectorConstantControls selector constant).map Prod.fst :=
          List.mem_map.mpr ⟨control, controlMember, rfl⟩
        have mapEq :
            (selectorConstantControls selector constant).map Prod.fst = selector := by
          simp [selectorConstantControls]
        rw [mapEq] at mapped
        exact mapped
      exact List.mem_append_left _ wireMember
    · intro wire member
      exact List.mem_append_right selector
        (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
    · exact List.mem_append_right selector
        (oracleSelectedWire_mem_diagonalOracleWorkWires p)
  · apply circuitUsesOnly_positiveMultiControlledX
    · intro wire member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact List.mem_append_right selector
          (oracleLegalWire_mem_diagonalOracleWorkWires p)
      · exact List.mem_append_right selector
          (oracleSelectedWire_mem_diagonalOracleWorkWires p)
      · exact List.mem_append_right selector
          (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
    · intro wire member
      exact List.mem_append_right selector
        (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
    · exact List.mem_append_right selector
        (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- column 対角 compute は定義した column support だけを参照する。 -/
theorem columnDiagonalCompute_usesOnly
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    circuitUsesOnly (columnDiagonalComputeSupport p)
      (xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
        (6 * slot.val + copy.val)) := by
  exact xorSelectorMatchIntoBranchFlagCircuit_usesOnly p (columnSelectorWires p) slot
    (6 * slot.val + copy.val)

/-- row 対角 compute は定義した row support だけを参照する。 -/
theorem rowDiagonalCompute_usesOnly
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    circuitUsesOnly (rowDiagonalComputeSupport p)
      (xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
        (6 * slot.val + copy.val)) := by
  exact xorSelectorMatchIntoBranchFlagCircuit_usesOnly p (rowSelectorWires p) slot
    (6 * slot.val + copy.val)

/-- row-output wire 列の長さは system 幅である。 -/
@[simp] theorem rowOutputWires_length (p : QParameters) :
    (rowOutputWires p).length = p.systemWidth := by
  simp [rowOutputWires]

/-- row-output wire 列には重複がない。 -/
theorem rowOutputWires_nodup (p : QParameters) :
    (rowOutputWires p).Nodup := by
  let slice := (QLayout.canonical p).rowOutput
  simpa [rowOutputWires, rowOutputWire, slice, RegisterSlice.wireList] using
    (slice.wireList_nodup :
      (slice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup)

/-- selector-output wire 列には重複がない。 -/
theorem selectorOutputWires_nodup (p : QParameters) :
    (selectorOutputWires p).Nodup := by
  let slice := (QLayout.canonical p).selectorOutput
  simpa [selectorOutputWires, selectorOutputWire, slice,
    RegisterSlice.wireList] using
      (slice.wireList_nodup :
        (slice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup)

/-- column-selector wire 列には重複がない。 -/
theorem columnSelectorWires_nodup (p : QParameters) :
    (columnSelectorWires p).Nodup := by
  let slice := (QLayout.canonical p).columnSelector
  simpa [columnSelectorWires, columnSelectorWire, slice,
    RegisterSlice.wireList] using
      (slice.wireList_nodup :
        (slice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup)

/-- column key と row output は異なる最上位 slice である。 -/
theorem columnKeyWires_disjoint_rowOutputWires (p : QParameters) :
    (columnKeyWires p).Disjoint (rowOutputWires p) := by
  let source := (QLayout.canonical p).columnKey
  let target := (QLayout.canonical p).rowOutput
  have disjoint :
      (source.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (target.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    source.wireList_disjoint_of_end_le_start target
      (by simp [source, target, QLayout.canonical]; omega)
  simpa [columnKeyWires, columnKeyWire, rowOutputWires, rowOutputWire,
    source, target, RegisterSlice.wireList] using disjoint

/-- branch bit は column-key register に含まれない。 -/
theorem oracleBranchWire_not_mem_columnKeyWires (p : QParameters) :
    oracleBranchWire p ∉ columnKeyWires p := by
  have disjoint := columnKeyWires_disjoint_oracleSlice p
    (OracleWorkLayout.canonical p).branch
  intro member
  apply (List.disjoint_left.mp disjoint) member
  let branch := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  change branch.ancillaWire 0 ∈
    (branch.wireList : List (Wire p.ancillaWidth p.systemWidth))
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- branch bit は物理 system register に含まれない。 -/
theorem oracleBranchWire_not_mem_systemWires (p : QParameters) :
    oracleBranchWire p ∉ systemWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _indexMember, equal⟩
  cases equal

/-- branch bit は row-output register に含まれない。 -/
theorem oracleBranchWire_not_mem_rowOutputWires (p : QParameters) :
    oracleBranchWire p ∉ rowOutputWires p := by
  exact fun member => (List.disjoint_left.mp
    (columnDiagonalSupport_disjoint_rowOutput p))
      (List.mem_append_right (columnSelectorWires p)
        (oracleBranchWire_mem_diagonalOracleWorkWires p)) member

/-- branch bit は selector-output register に含まれない。 -/
theorem oracleBranchWire_not_mem_selectorOutputWires (p : QParameters) :
    oracleBranchWire p ∉ selectorOutputWires p := by
  exact fun member => (List.disjoint_left.mp
    (columnDiagonalSupport_disjoint_selectorOutput p))
      (List.mem_append_right (columnSelectorWires p)
        (oracleBranchWire_mem_diagonalOracleWorkWires p)) member

/-- branch bit は column-selector register に含まれない。 -/
theorem oracleBranchWire_not_mem_columnSelectorWires (p : QParameters) :
    oracleBranchWire p ∉ columnSelectorWires p := by
  exact fun member => (List.disjoint_left.mp
    (rowDiagonalSupport_disjoint_columnSelector p))
      (List.mem_append_right (rowSelectorWires p)
        (oracleBranchWire_mem_diagonalOracleWorkWires p)) member

/-- branch bit と negative bit は異なる。 -/
theorem oracleBranchWire_ne_negativeWire (p : QParameters) :
    oracleBranchWire p ≠ negativeWire p := by
  intro equal
  apply negativeWire_not_mem_columnDiagonalSupport p
  rw [← equal]
  exact List.mem_append_right (columnSelectorWires p)
    (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- branch bit と active bit は異なる。 -/
theorem oracleBranchWire_ne_activeWire (p : QParameters) :
    oracleBranchWire p ≠ activeWire p := by
  intro equal
  apply activeWire_not_mem_columnDiagonalSupport p
  rw [← equal]
  exact List.mem_append_right (columnSelectorWires p)
    (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- branch bit と key-signal bit は異なる。 -/
theorem oracleBranchWire_ne_keySignalWire (p : QParameters) :
    oracleBranchWire p ≠ keySignalWire p := by
  intro equal
  apply keySignalWire_not_mem_rowDiagonalSupport p
  rw [← equal]
  exact List.mem_append_right (rowSelectorWires p)
    (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- column use は column compute support 上の値を保存する。 -/
theorem columnDiagonalBranchUse_preserves_support
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (columnDiagonalComputeSupport p)
      ((controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis
        reversibleGatePermutation input) input := by
  intro wire supportMember
  have outsideRow : wire ∉ rowOutputWires p := fun member =>
    (List.disjoint_left.mp (columnDiagonalSupport_disjoint_rowOutput p))
      supportMember member
  have outsideSelector : wire ∉ selectorOutputWires p := fun member =>
    (List.disjoint_left.mp (columnDiagonalSupport_disjoint_selectorOutput p))
      supportMember member
  have wireNeNegative : wire ≠ negativeWire p := by
    intro equal
    subst wire
    exact negativeWire_not_mem_columnDiagonalSupport p supportMember
  have wireNeActive : wire ≠ activeWire p := by
    intro equal
    subst wire
    exact activeWire_not_mem_columnDiagonalSupport p supportMember
  simp only [controlledXorColumnDiagonalResultIntoOutputsCircuit, runBasis_seq]
  rw [runBasis_safeCnot_outside (oracleBranchWire p) (activeWire p) wire
    (oracleBranchWire_ne_activeWire p) wireNeActive]
  rw [runBasis_safeCnot_outside (oracleBranchWire p) (negativeWire p) wire
    (oracleBranchWire_ne_negativeWire p) wireNeNegative]
  rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
    (selectorOutputWires p) (6 * slot.val + copy.val) _
    (oracleBranchWire_not_mem_selectorOutputWires p) wire outsideSelector]
  exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
    (columnKeyWires p) (rowOutputWires p) input
    (columnKeyWires_nodup p) (rowOutputWires_nodup p)
    (by simp) (columnKeyWires_disjoint_rowOutputWires p)
    (oracleBranchWire_not_mem_columnKeyWires p)
    (oracleBranchWire_not_mem_rowOutputWires p) wire outsideRow

/-- row use は row compute support 上の値を保存する。 -/
theorem rowDiagonalBranchUse_preserves_support
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (rowDiagonalComputeSupport p)
      ((controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis
        reversibleGatePermutation input) input := by
  intro wire supportMember
  have outsideKey : wire ∉ columnKeyWires p := fun member =>
    (List.disjoint_left.mp (rowDiagonalSupport_disjoint_columnKey p))
      supportMember member
  have outsideSelector : wire ∉ columnSelectorWires p := fun member =>
    (List.disjoint_left.mp (rowDiagonalSupport_disjoint_columnSelector p))
      supportMember member
  have wireNeKeySignal : wire ≠ keySignalWire p := by
    intro equal
    subst wire
    exact keySignalWire_not_mem_rowDiagonalSupport p supportMember
  have systemDisjointKey : (systemWires p).Disjoint (columnKeyWires p) := by
    simpa [systemWires, topSystemWires, QLayout.systemWire,
      columnKeyWires_eq_topColumnKeyWires]
      using topSystemWires_disjoint_topColumnKeyWires p
  simp only [controlledXorRowDiagonalResultIntoOutputsCircuit, runBasis_seq]
  rw [runBasis_safeCnot_outside (oracleBranchWire p) (keySignalWire p) wire
    (oracleBranchWire_ne_keySignalWire p) wireNeKeySignal]
  rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
    (columnSelectorWires p) (6 * slot.val + copy.val) _
    (oracleBranchWire_not_mem_columnSelectorWires p) wire outsideSelector]
  exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
    (systemWires p) (columnKeyWires p) input
    (systemWires_nodup p) (columnKeyWires_nodup p)
    (by simp) systemDisjointKey
    (oracleBranchWire_not_mem_systemWires p)
    (oracleBranchWire_not_mem_columnKeyWires p) wire outsideKey

/-- column 対角分岐全体は support を入力へ戻し、support 外に use 結果を残す。 -/
theorem runBasis_columnDiagonalResultComputeUseUncomputeCircuit_restoreSupport
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input =
      restoreSupport (columnDiagonalComputeSupport p) input
        ((controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis
          reversibleGatePermutation
          ((xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
            (6 * slot.val + copy.val)).runBasis
              reversibleGatePermutation input)) := by
  rw [columnDiagonalResultComputeUseUncomputeCircuit_eq_computeUseUncompute]
  exact Circuit.computeUseUncompute_local_clean
    (columnDiagonalComputeSupport p)
    (xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
      (6 * slot.val + copy.val))
    (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy) input
    (columnDiagonalCompute_usesOnly p slot copy)
    (columnDiagonalBranchUse_preserves_support p slot copy _)

/-- row 対角分岐全体は support を入力へ戻し、support 外に use 結果を残す。 -/
theorem runBasis_rowDiagonalResultComputeUseUncomputeCircuit_restoreSupport
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input =
      restoreSupport (rowDiagonalComputeSupport p) input
        ((controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis
          reversibleGatePermutation
          ((xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
            (6 * slot.val + copy.val)).runBasis
              reversibleGatePermutation input)) := by
  rw [rowDiagonalResultComputeUseUncomputeCircuit_eq_computeUseUncompute]
  exact Circuit.computeUseUncompute_local_clean
    (rowDiagonalComputeSupport p)
    (xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
      (6 * slot.val + copy.val))
    (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy) input
    (rowDiagonalCompute_usesOnly p slot copy)
    (rowDiagonalBranchUse_preserves_support p slot copy _)

/-- control が 0 なら controlled 定数 XOR の純粋作用は恒等である。 -/
theorem controlledXorConstantBasisAction_of_control_false
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits) (constant start : Nat)
    (targets : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (controlFalse : input control = false)
    (controlAbsent : control ∉ targets) :
    controlledXorConstantBasisAction control constant start targets input = input := by
  induction targets generalizing input start with
  | nil => rfl
  | cons target targets inductionHypothesis =>
      have controlNeTarget : control ≠ target := by
        intro equal
        exact controlAbsent (by simp [equal])
      have controlAbsentTail : control ∉ targets := by
        intro member
        exact controlAbsent (by simp [member])
      unfold controlledXorConstantBasisAction
      by_cases bit : constant.testBit start = true
      · simp only [bit, if_true]
        have cnotIdentity : cnotBasisAction control target input = input := by
          funext wire
          simp [cnotBasisAction, controlFalse]
        rw [cnotIdentity]
        exact inductionHypothesis (start + 1) input controlFalse controlAbsentTail
      · have bitFalse := Bool.eq_false_of_not_eq_true bit
        simp only [bitFalse, Bool.false_eq_true, if_false]
        exact inductionHypothesis (start + 1) input controlFalse controlAbsentTail

/-- branch bit が 0 なら column use 全体は恒等である。 -/
theorem columnDiagonalBranchUse_of_branch_false
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchFalse : input (oracleBranchWire p) = false) :
    (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  have copyIdentity :
      (controlledXorCopy (oracleBranchWire p) (columnKeyWires p)
        (rowOutputWires p)).runBasis reversibleGatePermutation input = input := by
    exact runBasis_validatedControlledXorCopyLists_of_control_false
      (oracleBranchWire p) (columnKeyWires p) (rowOutputWires p) input
      (columnKeyWires_nodup p) (rowOutputWires_nodup p) (by simp)
      (columnKeyWires_disjoint_rowOutputWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)
      (oracleBranchWire_not_mem_rowOutputWires p) branchFalse
  simp only [controlledXorColumnDiagonalResultIntoOutputsCircuit, runBasis_seq, copyIdentity]
  rw [runBasis_controlledXorConstant (oracleBranchWire p)
    (selectorOutputWires p) (6 * slot.val + copy.val) input
    (oracleBranchWire_not_mem_selectorOutputWires p)]
  rw [controlledXorConstantBasisAction_of_control_false
    (oracleBranchWire p) (6 * slot.val + copy.val) 0
    (selectorOutputWires p) input branchFalse
    (oracleBranchWire_not_mem_selectorOutputWires p)]
  rw [runBasis_safeCnot (oracleBranchWire p) (negativeWire p)
    (oracleBranchWire_ne_negativeWire p)]
  have negativeIdentity : cnotBasisAction (oracleBranchWire p)
      (negativeWire p) input = input := by
    funext wire
    simp [cnotBasisAction, branchFalse]
  rw [negativeIdentity]
  rw [runBasis_safeCnot (oracleBranchWire p) (activeWire p)
    (oracleBranchWire_ne_activeWire p)]
  funext wire
  simp [cnotBasisAction, branchFalse]

/-- branch bit が 0 なら row use 全体は恒等である。 -/
theorem rowDiagonalBranchUse_of_branch_false
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchFalse : input (oracleBranchWire p) = false) :
    (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  have systemDisjointKey : (systemWires p).Disjoint (columnKeyWires p) := by
    simpa [systemWires, topSystemWires, QLayout.systemWire,
      columnKeyWires_eq_topColumnKeyWires]
      using topSystemWires_disjoint_topColumnKeyWires p
  have copyIdentity :
      (controlledXorCopy (oracleBranchWire p) (systemWires p)
        (columnKeyWires p)).runBasis reversibleGatePermutation input = input := by
    exact runBasis_validatedControlledXorCopyLists_of_control_false
      (oracleBranchWire p) (systemWires p) (columnKeyWires p) input
      (systemWires_nodup p) (columnKeyWires_nodup p) (by simp) systemDisjointKey
      (oracleBranchWire_not_mem_systemWires p)
      (oracleBranchWire_not_mem_columnKeyWires p) branchFalse
  simp only [controlledXorRowDiagonalResultIntoOutputsCircuit, runBasis_seq, copyIdentity]
  rw [runBasis_controlledXorConstant (oracleBranchWire p)
    (columnSelectorWires p) (6 * slot.val + copy.val) input
    (oracleBranchWire_not_mem_columnSelectorWires p)]
  rw [controlledXorConstantBasisAction_of_control_false
    (oracleBranchWire p) (6 * slot.val + copy.val) 0
    (columnSelectorWires p) input branchFalse
    (oracleBranchWire_not_mem_columnSelectorWires p)]
  rw [runBasis_safeCnot (oracleBranchWire p) (keySignalWire p)
    (oracleBranchWire_ne_keySignalWire p)]
  funext wire
  simp [cnotBasisAction, branchFalse]

/-- row-output と selector-output は隣接する異なる slice である。 -/
theorem rowOutputWires_disjoint_selectorOutputWires (p : QParameters) :
    (rowOutputWires p).Disjoint (selectorOutputWires p) := by
  let left := (QLayout.canonical p).rowOutput
  let right := (QLayout.canonical p).selectorOutput
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  simpa [rowOutputWires, rowOutputWire, selectorOutputWires,
    selectorOutputWire, left, right, RegisterSlice.wireList] using disjoint

/-- negative bit は row-output register に含まれない。 -/
theorem negativeWire_not_mem_rowOutputWires (p : QParameters) :
    negativeWire p ∉ rowOutputWires p := by
  let left := (QLayout.canonical p).rowOutput
  let right := (QLayout.canonical p).negative
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  have member : negativeWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [rowOutputWires, rowOutputWire, left,
      RegisterSlice.wireList] using leftMember) member

/-- active bit は row-output register に含まれない。 -/
theorem activeWire_not_mem_rowOutputWires (p : QParameters) :
    activeWire p ∉ rowOutputWires p := by
  let left := (QLayout.canonical p).rowOutput
  let right := (QLayout.canonical p).active
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  have member : activeWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [rowOutputWires, rowOutputWire, left,
      RegisterSlice.wireList] using leftMember) member

/-- negative bit は selector-output register に含まれない。 -/
theorem negativeWire_not_mem_selectorOutputWires (p : QParameters) :
    negativeWire p ∉ selectorOutputWires p := by
  let left := (QLayout.canonical p).selectorOutput
  let right := (QLayout.canonical p).negative
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  have member : negativeWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [selectorOutputWires, selectorOutputWire, left,
      RegisterSlice.wireList] using leftMember) member

/-- active bit は selector-output register に含まれない。 -/
theorem activeWire_not_mem_selectorOutputWires (p : QParameters) :
    activeWire p ∉ selectorOutputWires p := by
  let left := (QLayout.canonical p).selectorOutput
  let right := (QLayout.canonical p).active
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  have member : activeWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [selectorOutputWires, selectorOutputWire, left,
      RegisterSlice.wireList] using leftMember) member

/-- negative bit と active bit は異なる。 -/
theorem negativeWire_ne_activeWire (p : QParameters) :
    negativeWire p ≠ activeWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [negativeWire, activeWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers

/-- column-key と column-selector は異なる最上位 slice である。 -/
theorem columnKeyWires_disjoint_columnSelectorWires (p : QParameters) :
    (columnKeyWires p).Disjoint (columnSelectorWires p) := by
  let left := (QLayout.canonical p).columnKey
  let right := (QLayout.canonical p).columnSelector
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical])
  simpa [columnKeyWires, columnKeyWire, columnSelectorWires,
    columnSelectorWire, left, right, RegisterSlice.wireList] using disjoint

/-- key-signal bit は column-key register に含まれない。 -/
theorem keySignalWire_not_mem_columnKeyWires (p : QParameters) :
    keySignalWire p ∉ columnKeyWires p := by
  let left := (QLayout.canonical p).columnKey
  let right := (QLayout.canonical p).keySignal
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical])
  have member : keySignalWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [columnKeyWires, columnKeyWire, left,
      RegisterSlice.wireList] using leftMember) member

/-- key-signal bit は column-selector register に含まれない。 -/
theorem keySignalWire_not_mem_columnSelectorWires (p : QParameters) :
    keySignalWire p ∉ columnSelectorWires p := by
  let left := (QLayout.canonical p).columnSelector
  let right := (QLayout.canonical p).keySignal
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  have member : keySignalWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [columnSelectorWires, columnSelectorWire, left,
      RegisterSlice.wireList] using leftMember) member

/-- support 外の重複なし register は局所回路の実行前後で同じ値を読む。 -/
theorem readWires_runBasis_of_usesOnly_disjoint
    {ancillaQubits systemQubits : Nat}
    (support wires : List (Wire ancillaQubits systemQubits))
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (usesOnly : circuitUsesOnly support circuit)
    (disjoint : support.Disjoint wires) :
    readWires wires (circuit.runBasis reversibleGatePermutation input) =
      readWires wires input := by
  apply List.map_congr_left
  intro wire member
  apply Circuit.runBasis_outside_of_usesOnly support circuit usesOnly input wire
  intro supportMember
  exact (List.disjoint_left.mp disjoint) supportMember member

/-- column use の四出力をまとめた XOR 仕様。 -/
structure ColumnDiagonalUseResult (p : QParameters) (constant : Nat)
    (enabled : Bool) (input output : JointBasis p.ancillaWidth p.systemWidth) :
    Prop where
  /-- row-output は有効時だけ column-key と bitwise XOR される。 -/
  row_output : readWires (rowOutputWires p) output =
    if enabled then
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires (columnKeyWires p) input)
        (readWires (rowOutputWires p) input)
    else readWires (rowOutputWires p) input
  /-- selector-output は有効時だけ定数 selector と XOR される。 -/
  selector_output : readWires (selectorOutputWires p) output =
    controlledXorConstantBits enabled constant 0
      (readWires (selectorOutputWires p) input)
  /-- negative bit は有効時だけ反転する。 -/
  negative : output (negativeWire p) =
    if enabled then !(input (negativeWire p)) else input (negativeWire p)
  /-- active bit は有効時だけ反転する。 -/
  active : output (activeWire p) =
    if enabled then !(input (activeWire p)) else input (activeWire p)

/-- row use の三出力をまとめた XOR 仕様。 -/
structure RowDiagonalUseResult (p : QParameters) (constant : Nat)
    (enabled : Bool) (input output : JointBasis p.ancillaWidth p.systemWidth) :
    Prop where
  /-- column-key は有効時だけ system と bitwise XOR される。 -/
  column_key : readWires (columnKeyWires p) output =
    if enabled then
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires (systemWires p) input)
        (readWires (columnKeyWires p) input)
    else readWires (columnKeyWires p) input
  /-- column-selector は有効時だけ定数 selector と XOR される。 -/
  column_selector : readWires (columnSelectorWires p) output =
    controlledXorConstantBits enabled constant 0
      (readWires (columnSelectorWires p) input)
  /-- key-signal bit は有効時だけ反転する。 -/
  key_signal : output (keySignalWire p) =
    if enabled then !(input (keySignalWire p)) else input (keySignalWire p)

/-- controlled 定数 XOR は target と交わらない任意 register を保存する。 -/
theorem readWires_controlledXorConstant_of_disjoint
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (targets wires : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (controlAbsent : control ∉ targets)
    (wiresDisjointTargets : wires.Disjoint targets) :
    readWires wires
        ((controlledXorConstant control targets constant).runBasis
          reversibleGatePermutation input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_controlledXorConstant_outside control targets constant input
    controlAbsent wire (fun targetMember =>
      (List.disjoint_left.mp wiresDisjointTargets) member targetMember)

/-- safe CNOT は target を含まない任意 register を保存する。 -/
theorem readWires_safeCnot_of_target_not_mem
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (controlDifferent : control ≠ target) (targetAbsent : target ∉ wires) :
    readWires wires ((safeCnot control target).runBasis
      reversibleGatePermutation input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_safeCnot_outside control target wire controlDifferent
    (fun equal => targetAbsent (equal ▸ member)) input

/-- column use は branch 値に応じて四出力を厳密に XOR する。 -/
theorem columnDiagonalBranchUse_correct
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2) (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchValue : input (oracleBranchWire p) = enabled) :
    ColumnDiagonalUseResult p (6 * slot.val + copy.val) enabled input
      ((controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  let copied := (controlledXorCopy (oracleBranchWire p)
    (columnKeyWires p) (rowOutputWires p)).runBasis
      reversibleGatePermutation input
  let encoded := (controlledXorConstant (oracleBranchWire p)
    (selectorOutputWires p) (6 * slot.val + copy.val)).runBasis
      reversibleGatePermutation copied
  let signed := (safeCnot (oracleBranchWire p) (negativeWire p)).runBasis
    reversibleGatePermutation encoded
  have copyLayoutLength : (columnKeyWires p).length = (rowOutputWires p).length := by
    simp
  have copiedBranch : copied (oracleBranchWire p) = enabled := by
    rw [show copied (oracleBranchWire p) = input (oracleBranchWire p) by
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (columnKeyWires p) (rowOutputWires p) input
        (columnKeyWires_nodup p) (rowOutputWires_nodup p) copyLayoutLength
        (columnKeyWires_disjoint_rowOutputWires p)
        (oracleBranchWire_not_mem_columnKeyWires p)
        (oracleBranchWire_not_mem_rowOutputWires p) (oracleBranchWire p)
        (oracleBranchWire_not_mem_rowOutputWires p)]
    exact branchValue
  have copiedSelector : readWires (selectorOutputWires p) copied =
      readWires (selectorOutputWires p) input := by
    exact readWires_validatedControlledXorCopyLists_outside (oracleBranchWire p)
      (columnKeyWires p) (rowOutputWires p) (selectorOutputWires p) input
      (columnKeyWires_nodup p) (rowOutputWires_nodup p)
      copyLayoutLength (columnKeyWires_disjoint_rowOutputWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)
      (oracleBranchWire_not_mem_rowOutputWires p)
      (rowOutputWires_disjoint_selectorOutputWires p).symm
  have encodedBranch : encoded (oracleBranchWire p) = enabled := by
    rw [show encoded (oracleBranchWire p) = copied (oracleBranchWire p) by
      exact runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (selectorOutputWires p) (6 * slot.val + copy.val) copied
        (oracleBranchWire_not_mem_selectorOutputWires p)
        (oracleBranchWire p) (oracleBranchWire_not_mem_selectorOutputWires p)]
    exact copiedBranch
  have signedBranch : signed (oracleBranchWire p) = enabled := by
    rw [show signed (oracleBranchWire p) = encoded (oracleBranchWire p) by
      exact runBasis_safeCnot_outside (oracleBranchWire p) (negativeWire p)
        (oracleBranchWire p) (oracleBranchWire_ne_negativeWire p)
        (oracleBranchWire_ne_negativeWire p) encoded]
    exact encodedBranch
  change ColumnDiagonalUseResult p (6 * slot.val + copy.val) enabled input
    ((safeCnot (oracleBranchWire p) (activeWire p)).runBasis
      reversibleGatePermutation signed)
  constructor
  · rw [readWires_safeCnot_of_target_not_mem (oracleBranchWire p)
      (activeWire p) (rowOutputWires p) signed
      (oracleBranchWire_ne_activeWire p) (activeWire_not_mem_rowOutputWires p)]
    rw [readWires_safeCnot_of_target_not_mem (oracleBranchWire p)
      (negativeWire p) (rowOutputWires p) encoded
      (oracleBranchWire_ne_negativeWire p) (negativeWire_not_mem_rowOutputWires p)]
    rw [readWires_controlledXorConstant_of_disjoint (oracleBranchWire p)
      (selectorOutputWires p) (rowOutputWires p) (6 * slot.val + copy.val)
      copied (oracleBranchWire_not_mem_selectorOutputWires p)
      (rowOutputWires_disjoint_selectorOutputWires p)]
    rw [readWires_validatedControlledXorCopyLists_target (oracleBranchWire p)
      (columnKeyWires p) (rowOutputWires p) input
      (columnKeyWires_nodup p) (rowOutputWires_nodup p) copyLayoutLength
      (columnKeyWires_disjoint_rowOutputWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)
      (oracleBranchWire_not_mem_rowOutputWires p)]
    rw [branchValue]
  · rw [readWires_safeCnot_of_target_not_mem (oracleBranchWire p)
      (activeWire p) (selectorOutputWires p) signed
      (oracleBranchWire_ne_activeWire p)
      (activeWire_not_mem_selectorOutputWires p)]
    rw [readWires_safeCnot_of_target_not_mem (oracleBranchWire p)
      (negativeWire p) (selectorOutputWires p) encoded
      (oracleBranchWire_ne_negativeWire p)
      (negativeWire_not_mem_selectorOutputWires p)]
    rw [readWires_controlledXorConstant (oracleBranchWire p)
      (selectorOutputWires p) (6 * slot.val + copy.val) copied
      (selectorOutputWires_nodup p)
      (oracleBranchWire_not_mem_selectorOutputWires p)]
    rw [copiedBranch, copiedSelector]
  · rw [runBasis_safeCnot (oracleBranchWire p) (activeWire p)
      (oracleBranchWire_ne_activeWire p)]
    rw [cnotBasisAction_other (oracleBranchWire p) (activeWire p)
      (negativeWire p) (negativeWire_ne_activeWire p)]
    dsimp [signed]
    rw [runBasis_safeCnot (oracleBranchWire p) (negativeWire p)
      (oracleBranchWire_ne_negativeWire p)]
    rw [cnotBasisAction_target]
    have encodedNegative : encoded (negativeWire p) = input (negativeWire p) := by
      dsimp [encoded]
      rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (selectorOutputWires p) (6 * slot.val + copy.val) copied
        (oracleBranchWire_not_mem_selectorOutputWires p) (negativeWire p)
        (negativeWire_not_mem_selectorOutputWires p)]
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (columnKeyWires p) (rowOutputWires p) input
        (columnKeyWires_nodup p) (rowOutputWires_nodup p) copyLayoutLength
        (columnKeyWires_disjoint_rowOutputWires p)
        (oracleBranchWire_not_mem_columnKeyWires p)
        (oracleBranchWire_not_mem_rowOutputWires p) (negativeWire p)
        (negativeWire_not_mem_rowOutputWires p)
    rw [encodedBranch, encodedNegative]
  · rw [runBasis_safeCnot (oracleBranchWire p) (activeWire p)
      (oracleBranchWire_ne_activeWire p)]
    rw [cnotBasisAction_target, signedBranch]
    have signedActive : signed (activeWire p) = input (activeWire p) := by
      dsimp [signed]
      rw [runBasis_safeCnot_outside (oracleBranchWire p) (negativeWire p)
        (activeWire p) (oracleBranchWire_ne_negativeWire p)
        (negativeWire_ne_activeWire p).symm encoded]
      dsimp [encoded]
      rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (selectorOutputWires p) (6 * slot.val + copy.val) copied
        (oracleBranchWire_not_mem_selectorOutputWires p) (activeWire p)
        (activeWire_not_mem_selectorOutputWires p)]
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (columnKeyWires p) (rowOutputWires p) input
        (columnKeyWires_nodup p) (rowOutputWires_nodup p) copyLayoutLength
        (columnKeyWires_disjoint_rowOutputWires p)
        (oracleBranchWire_not_mem_columnKeyWires p)
        (oracleBranchWire_not_mem_rowOutputWires p) (activeWire p)
        (activeWire_not_mem_rowOutputWires p)
    rw [signedActive]

/-- row use は branch 値に応じて三出力を厳密に XOR する。 -/
theorem rowDiagonalBranchUse_correct
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2) (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchValue : input (oracleBranchWire p) = enabled) :
    RowDiagonalUseResult p (6 * slot.val + copy.val) enabled input
      ((controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  let copied := (controlledXorCopy (oracleBranchWire p)
    (systemWires p) (columnKeyWires p)).runBasis
      reversibleGatePermutation input
  let encoded := (controlledXorConstant (oracleBranchWire p)
    (columnSelectorWires p) (6 * slot.val + copy.val)).runBasis
      reversibleGatePermutation copied
  have systemDisjointKey : (systemWires p).Disjoint (columnKeyWires p) := by
    simpa [systemWires, topSystemWires, QLayout.systemWire,
      columnKeyWires_eq_topColumnKeyWires]
      using topSystemWires_disjoint_topColumnKeyWires p
  have copyLayoutLength : (systemWires p).length = (columnKeyWires p).length := by
    simp
  have copiedBranch : copied (oracleBranchWire p) = enabled := by
    rw [show copied (oracleBranchWire p) = input (oracleBranchWire p) by
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (systemWires p) (columnKeyWires p) input
        (systemWires_nodup p) (columnKeyWires_nodup p) copyLayoutLength
        systemDisjointKey (oracleBranchWire_not_mem_systemWires p)
        (oracleBranchWire_not_mem_columnKeyWires p) (oracleBranchWire p)
        (oracleBranchWire_not_mem_columnKeyWires p)]
    exact branchValue
  have copiedSelector : readWires (columnSelectorWires p) copied =
      readWires (columnSelectorWires p) input := by
    exact readWires_validatedControlledXorCopyLists_outside (oracleBranchWire p)
      (systemWires p) (columnKeyWires p) (columnSelectorWires p) input
      (systemWires_nodup p) (columnKeyWires_nodup p)
      copyLayoutLength systemDisjointKey (oracleBranchWire_not_mem_systemWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)
      (columnKeyWires_disjoint_columnSelectorWires p).symm
  have encodedBranch : encoded (oracleBranchWire p) = enabled := by
    rw [show encoded (oracleBranchWire p) = copied (oracleBranchWire p) by
      exact runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (columnSelectorWires p) (6 * slot.val + copy.val) copied
        (oracleBranchWire_not_mem_columnSelectorWires p)
        (oracleBranchWire p) (oracleBranchWire_not_mem_columnSelectorWires p)]
    exact copiedBranch
  change RowDiagonalUseResult p (6 * slot.val + copy.val) enabled input
    ((safeCnot (oracleBranchWire p) (keySignalWire p)).runBasis
      reversibleGatePermutation encoded)
  constructor
  · rw [readWires_safeCnot_of_target_not_mem (oracleBranchWire p)
      (keySignalWire p) (columnKeyWires p) encoded
      (oracleBranchWire_ne_keySignalWire p)
      (keySignalWire_not_mem_columnKeyWires p)]
    rw [readWires_controlledXorConstant_of_disjoint (oracleBranchWire p)
      (columnSelectorWires p) (columnKeyWires p) (6 * slot.val + copy.val)
      copied (oracleBranchWire_not_mem_columnSelectorWires p)
      (columnKeyWires_disjoint_columnSelectorWires p)]
    rw [readWires_validatedControlledXorCopyLists_target (oracleBranchWire p)
      (systemWires p) (columnKeyWires p) input
      (systemWires_nodup p) (columnKeyWires_nodup p)
      copyLayoutLength systemDisjointKey
      (oracleBranchWire_not_mem_systemWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)]
    rw [branchValue]
  · rw [readWires_safeCnot_of_target_not_mem (oracleBranchWire p)
      (keySignalWire p) (columnSelectorWires p) encoded
      (oracleBranchWire_ne_keySignalWire p)
      (keySignalWire_not_mem_columnSelectorWires p)]
    rw [readWires_controlledXorConstant (oracleBranchWire p)
      (columnSelectorWires p) (6 * slot.val + copy.val) copied
      (columnSelectorWires_nodup p)
      (oracleBranchWire_not_mem_columnSelectorWires p)]
    rw [copiedBranch, copiedSelector]
  · rw [runBasis_safeCnot (oracleBranchWire p) (keySignalWire p)
      (oracleBranchWire_ne_keySignalWire p)]
    rw [cnotBasisAction_target, encodedBranch]
    have encodedSignal : encoded (keySignalWire p) = input (keySignalWire p) := by
      dsimp [encoded]
      rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (columnSelectorWires p) (6 * slot.val + copy.val) copied
        (oracleBranchWire_not_mem_columnSelectorWires p) (keySignalWire p)
        (keySignalWire_not_mem_columnSelectorWires p)]
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (systemWires p) (columnKeyWires p) input
        (systemWires_nodup p) (columnKeyWires_nodup p) copyLayoutLength
        systemDisjointKey (oracleBranchWire_not_mem_systemWires p)
        (oracleBranchWire_not_mem_columnKeyWires p) (keySignalWire p)
        (keySignalWire_not_mem_columnKeyWires p)
    rw [encodedSignal]

/-- column compute support は column-key register と交わらない。 -/
theorem columnDiagonalSupport_disjoint_columnKey (p : QParameters) :
    (columnDiagonalComputeSupport p).Disjoint (columnKeyWires p) := by
  let selector := (QLayout.canonical p).columnSelector
  let target := (QLayout.canonical p).columnKey
  have targetSelectorDisjoint :
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (selector.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    target.wireList_disjoint_of_end_le_start selector
      (by simp [selector, target, QLayout.canonical])
  have targetWorkDisjoint :
      (target.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    target.wireList_disjoint_of_end_le_start (QLayout.canonical p).oracleWork
      (by simp [target, QLayout.canonical]; omega)
  rw [List.disjoint_left]
  intro wire supportMember targetMember
  rcases List.mem_append.mp supportMember with selectorMember | workMember
  · exact (List.disjoint_left.mp targetSelectorDisjoint) targetMember
      (by simpa [columnDiagonalComputeSupport, columnSelectorWires,
        columnSelectorWire, selector, RegisterSlice.wireList] using selectorMember)
  · exact (List.disjoint_left.mp targetWorkDisjoint) targetMember workMember

/-- row compute support は物理 system register と交わらない。 -/
theorem rowDiagonalSupport_disjoint_systemWires (p : QParameters) :
    (rowDiagonalComputeSupport p).Disjoint (systemWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember systemMember
  rcases List.mem_map.mp systemMember with ⟨index, _indexMember, equal⟩
  rcases List.mem_append.mp supportMember with selectorMember | workMember
  · rcases List.mem_map.mp selectorMember with ⟨selectorIndex, _, selectorEqual⟩
    cases equal.trans selectorEqual.symm
  · rcases List.mem_map.mp workMember with ⟨workIndex, _, workEqual⟩
    cases equal.trans workEqual.symm

/-- column 対角分岐全体の XOR 出力と一時領域復元仕様。 -/
structure ColumnDiagonalResultWithWorkRestorationSpec (p : QParameters) (constant : Nat)
    (enabled : Bool) (input output : JointBasis p.ancillaWidth p.systemWidth) :
    Prop extends ColumnDiagonalUseResult p constant enabled input output where
  /-- selected 一時 bit は入力値へ戻る。 -/
  selected_restored : output (oracleSelectedWire p) = input (oracleSelectedWire p)
  /-- branch 一時 bit は入力値へ戻る。 -/
  branch_restored : output (oracleBranchWire p) = input (oracleBranchWire p)
  /-- decoder AND scratch は各 wire で入力値へ戻る。 -/
  scratch_restored : ∀ wire ∈ decoderAndScratchWires p, output wire = input wire

/-- row 対角分岐全体の XOR 出力と一時領域復元仕様。 -/
structure RowDiagonalResultWithWorkRestorationSpec (p : QParameters) (constant : Nat)
    (enabled : Bool) (input output : JointBasis p.ancillaWidth p.systemWidth) :
    Prop extends RowDiagonalUseResult p constant enabled input output where
  /-- selected 一時 bit は入力値へ戻る。 -/
  selected_restored : output (oracleSelectedWire p) = input (oracleSelectedWire p)
  /-- branch 一時 bit は入力値へ戻る。 -/
  branch_restored : output (oracleBranchWire p) = input (oracleBranchWire p)
  /-- decoder AND scratch は各 wire で入力値へ戻る。 -/
  scratch_restored : ∀ wire ∈ decoderAndScratchWires p, output wire = input wire

/-- column 対角分岐は一般 clean 入力で XOR 出力を満たし、一時領域を消去する。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_correct
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    ColumnDiagonalResultWithWorkRestorationSpec p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input)
      input ((columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  let enabled := diagonalBranchEnabled p (columnSelectorWires p) slot
    (6 * slot.val + copy.val) legalValue presentValue input
  let compute := xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
    (6 * slot.val + copy.val)
  let computed := selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
    (6 * slot.val + copy.val) input
  let used := (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis
    reversibleGatePermutation computed
  let output := (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
    reversibleGatePermutation input
  have computeRun : compute.runBasis reversibleGatePermutation input = computed := by
    exact runBasis_columnDiagonalCompute p slot copy input clean.scratch_zero
  have computedBranch : computed (oracleBranchWire p) = enabled := by
    exact selectorMatchBranchFlagXorReference_branch p (columnSelectorWires p) slot
      (6 * slot.val + copy.val) legalValue presentValue input clean
  have useSpec : ColumnDiagonalUseResult p (6 * slot.val + copy.val)
      enabled computed used :=
    columnDiagonalBranchUse_correct p slot copy enabled computed computedBranch
  have outputEq : output = restoreSupport (columnDiagonalComputeSupport p)
      input used := by
    dsimp [output, used, computed, compute]
    rw [runBasis_columnDiagonalResultComputeUseUncomputeCircuit_restoreSupport p slot copy input]
    rw [runBasis_columnDiagonalCompute p slot copy input clean.scratch_zero]
  have keyComputed : readWires (columnKeyWires p) computed =
      readWires (columnKeyWires p) input := by
    rw [← computeRun]
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnDiagonalComputeSupport p) (columnKeyWires p) compute input
      (columnDiagonalCompute_usesOnly p slot copy)
      (columnDiagonalSupport_disjoint_columnKey p)
  have rowComputed : readWires (rowOutputWires p) computed =
      readWires (rowOutputWires p) input := by
    rw [← computeRun]
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnDiagonalComputeSupport p) (rowOutputWires p) compute input
      (columnDiagonalCompute_usesOnly p slot copy)
      (columnDiagonalSupport_disjoint_rowOutput p)
  have selectorComputed : readWires (selectorOutputWires p) computed =
      readWires (selectorOutputWires p) input := by
    rw [← computeRun]
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnDiagonalComputeSupport p) (selectorOutputWires p) compute input
      (columnDiagonalCompute_usesOnly p slot copy)
      (columnDiagonalSupport_disjoint_selectorOutput p)
  have negativeComputed : computed (negativeWire p) = input (negativeWire p) := by
    rw [← computeRun]
    exact Circuit.runBasis_outside_of_usesOnly (columnDiagonalComputeSupport p)
      compute (columnDiagonalCompute_usesOnly p slot copy) input (negativeWire p)
      (negativeWire_not_mem_columnDiagonalSupport p)
  have activeComputed : computed (activeWire p) = input (activeWire p) := by
    rw [← computeRun]
    exact Circuit.runBasis_outside_of_usesOnly (columnDiagonalComputeSupport p)
      compute (columnDiagonalCompute_usesOnly p slot copy) input (activeWire p)
      (activeWire_not_mem_columnDiagonalSupport p)
  have rowFinal : readWires (rowOutputWires p) output =
      readWires (rowOutputWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (columnDiagonalComputeSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (columnDiagonalSupport_disjoint_rowOutput p))
          supportMember member)
  have selectorFinal : readWires (selectorOutputWires p) output =
      readWires (selectorOutputWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (columnDiagonalComputeSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (columnDiagonalSupport_disjoint_selectorOutput p))
          supportMember member)
  have negativeFinal : output (negativeWire p) = used (negativeWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (columnDiagonalComputeSupport p) input used
      (negativeWire p) (negativeWire_not_mem_columnDiagonalSupport p)
  have activeFinal : output (activeWire p) = used (activeWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (columnDiagonalComputeSupport p) input used
      (activeWire p) (activeWire_not_mem_columnDiagonalSupport p)
  change ColumnDiagonalResultWithWorkRestorationSpec p (6 * slot.val + copy.val) enabled input output
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rowFinal, useSpec.row_output, keyComputed, rowComputed]
    · rw [selectorFinal, useSpec.selector_output, selectorComputed]
    · rw [negativeFinal, useSpec.negative, negativeComputed]
    · rw [activeFinal, useSpec.active, activeComputed]
  · rw [outputEq]
    exact restoreSupport_agrees_input (columnDiagonalComputeSupport p) input used
      (oracleSelectedWire p)
      (List.mem_append_right (columnSelectorWires p)
        (oracleSelectedWire_mem_diagonalOracleWorkWires p))
  · rw [outputEq]
    exact restoreSupport_agrees_input (columnDiagonalComputeSupport p) input used
      (oracleBranchWire p)
      (List.mem_append_right (columnSelectorWires p)
        (oracleBranchWire_mem_diagonalOracleWorkWires p))
  · intro wire member
    rw [outputEq]
    exact restoreSupport_agrees_input (columnDiagonalComputeSupport p) input used wire
      (List.mem_append_right (columnSelectorWires p)
        (decoderAndScratchWire_mem_diagonalOracleWorkWires p member))

/-- row 対角分岐は一般 clean 入力で XOR 出力を満たし、一時領域を消去する。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_correct
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    RowDiagonalResultWithWorkRestorationSpec p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input)
      input ((rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  let enabled := diagonalBranchEnabled p (rowSelectorWires p) slot
    (6 * slot.val + copy.val) legalValue presentValue input
  let compute := xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
    (6 * slot.val + copy.val)
  let computed := selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
    (6 * slot.val + copy.val) input
  let used := (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis
    reversibleGatePermutation computed
  let output := (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
    reversibleGatePermutation input
  have computeRun : compute.runBasis reversibleGatePermutation input = computed := by
    exact runBasis_rowDiagonalCompute p slot copy input clean.scratch_zero
  have computedBranch : computed (oracleBranchWire p) = enabled := by
    exact selectorMatchBranchFlagXorReference_branch p (rowSelectorWires p) slot
      (6 * slot.val + copy.val) legalValue presentValue input clean
  have useSpec : RowDiagonalUseResult p (6 * slot.val + copy.val)
      enabled computed used :=
    rowDiagonalBranchUse_correct p slot copy enabled computed computedBranch
  have outputEq : output = restoreSupport (rowDiagonalComputeSupport p)
      input used := by
    dsimp [output, used, computed, compute]
    rw [runBasis_rowDiagonalResultComputeUseUncomputeCircuit_restoreSupport p slot copy input]
    rw [runBasis_rowDiagonalCompute p slot copy input clean.scratch_zero]
  have systemComputed : readWires (systemWires p) computed =
      readWires (systemWires p) input := by
    rw [← computeRun]
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowDiagonalComputeSupport p) (systemWires p) compute input
      (rowDiagonalCompute_usesOnly p slot copy)
      (rowDiagonalSupport_disjoint_systemWires p)
  have keyComputed : readWires (columnKeyWires p) computed =
      readWires (columnKeyWires p) input := by
    rw [← computeRun]
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowDiagonalComputeSupport p) (columnKeyWires p) compute input
      (rowDiagonalCompute_usesOnly p slot copy)
      (rowDiagonalSupport_disjoint_columnKey p)
  have selectorComputed : readWires (columnSelectorWires p) computed =
      readWires (columnSelectorWires p) input := by
    rw [← computeRun]
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowDiagonalComputeSupport p) (columnSelectorWires p) compute input
      (rowDiagonalCompute_usesOnly p slot copy)
      (rowDiagonalSupport_disjoint_columnSelector p)
  have signalComputed : computed (keySignalWire p) = input (keySignalWire p) := by
    rw [← computeRun]
    exact Circuit.runBasis_outside_of_usesOnly (rowDiagonalComputeSupport p)
      compute (rowDiagonalCompute_usesOnly p slot copy) input (keySignalWire p)
      (keySignalWire_not_mem_rowDiagonalSupport p)
  have keyFinal : readWires (columnKeyWires p) output =
      readWires (columnKeyWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (rowDiagonalComputeSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (rowDiagonalSupport_disjoint_columnKey p))
          supportMember member)
  have selectorFinal : readWires (columnSelectorWires p) output =
      readWires (columnSelectorWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (rowDiagonalComputeSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (rowDiagonalSupport_disjoint_columnSelector p))
          supportMember member)
  have signalFinal : output (keySignalWire p) = used (keySignalWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (rowDiagonalComputeSupport p) input used
      (keySignalWire p) (keySignalWire_not_mem_rowDiagonalSupport p)
  change RowDiagonalResultWithWorkRestorationSpec p (6 * slot.val + copy.val) enabled input output
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [keyFinal, useSpec.column_key, systemComputed, keyComputed]
    · rw [selectorFinal, useSpec.column_selector, selectorComputed]
    · rw [signalFinal, useSpec.key_signal, signalComputed]
  · rw [outputEq]
    exact restoreSupport_agrees_input (rowDiagonalComputeSupport p) input used
      (oracleSelectedWire p)
      (List.mem_append_right (rowSelectorWires p)
        (oracleSelectedWire_mem_diagonalOracleWorkWires p))
  · rw [outputEq]
    exact restoreSupport_agrees_input (rowDiagonalComputeSupport p) input used
      (oracleBranchWire p)
      (List.mem_append_right (rowSelectorWires p)
        (oracleBranchWire_mem_diagonalOracleWorkWires p))
  · intro wire member
    rw [outputEq]
    exact restoreSupport_agrees_input (rowDiagonalComputeSupport p) input used wire
      (List.mem_append_right (rowSelectorWires p)
        (decoderAndScratchWire_mem_diagonalOracleWorkWires p member))

/-- column 対角分岐の有効条件が偽なら、全基底状態上で分岐全体は恒等である。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_inactive
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input)
    (inactive : diagonalBranchEnabled p (columnSelectorWires p) slot
      (6 * slot.val + copy.val) legalValue presentValue input = false) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  let compute := xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
    (6 * slot.val + copy.val)
  let computed := selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
    (6 * slot.val + copy.val) input
  have computeRun : compute.runBasis reversibleGatePermutation input = computed :=
    runBasis_columnDiagonalCompute p slot copy input clean.scratch_zero
  have branchFalse : computed (oracleBranchWire p) = false := by
    dsimp [computed]
    rw [selectorMatchBranchFlagXorReference_branch p (columnSelectorWires p) slot
      (6 * slot.val + copy.val) legalValue presentValue input clean]
    exact inactive
  rw [columnDiagonalResultComputeUseUncomputeCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute
    (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy) input input
  change (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation input) =
    compute.runBasis reversibleGatePermutation input
  rw [computeRun]
  exact columnDiagonalBranchUse_of_branch_false p slot copy computed branchFalse

/-- row 対角分岐の有効条件が偽なら、全基底状態上で分岐全体は恒等である。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_inactive
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input)
    (inactive : diagonalBranchEnabled p (rowSelectorWires p) slot
      (6 * slot.val + copy.val) legalValue presentValue input = false) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  let compute := xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
    (6 * slot.val + copy.val)
  let computed := selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
    (6 * slot.val + copy.val) input
  have computeRun : compute.runBasis reversibleGatePermutation input = computed :=
    runBasis_rowDiagonalCompute p slot copy input clean.scratch_zero
  have branchFalse : computed (oracleBranchWire p) = false := by
    dsimp [computed]
    rw [selectorMatchBranchFlagXorReference_branch p (rowSelectorWires p) slot
      (6 * slot.val + copy.val) legalValue presentValue input clean]
    exact inactive
  rw [rowDiagonalResultComputeUseUncomputeCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute
    (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy) input input
  change (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation input) =
    compute.runBasis reversibleGatePermutation input
  rw [computeRun]
  exact rowDiagonalBranchUse_of_branch_false p slot copy computed branchFalse

/-- column selector が対象定数と不一致なら padding/inactive 分岐は恒等である。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_padding_identity
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input)
    (mismatch : diagonalSelectorMatches (columnSelectorWires p)
      (6 * slot.val + copy.val) input = false) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  apply columnDiagonalResultComputeUseUncomputeCircuit_inactive p slot copy legalValue presentValue
    input clean
  simp [diagonalBranchEnabled, mismatch]

/-- row selector が対象定数と不一致なら padding/inactive 分岐は恒等である。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_padding_identity
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input)
    (mismatch : diagonalSelectorMatches (rowSelectorWires p)
      (6 * slot.val + copy.val) input = false) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  apply rowDiagonalResultComputeUseUncomputeCircuit_inactive p slot copy legalValue presentValue input clean
  simp [diagonalBranchEnabled, mismatch]

/-- selector・legal・present がすべて成立する column 分岐の明示的な active 系。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_active
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot true true input)
    (selectorMatch : diagonalSelectorMatches (columnSelectorWires p)
      (6 * slot.val + copy.val) input = true) :
    ColumnDiagonalResultWithWorkRestorationSpec p (6 * slot.val + copy.val) true input
      ((columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  have result := columnDiagonalResultComputeUseUncomputeCircuit_correct p slot copy true true input clean
  simpa [diagonalBranchEnabled, selectorMatch] using result

/-- selector・legal・present がすべて成立する row 分岐の明示的な active 系。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_active
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot true true input)
    (selectorMatch : diagonalSelectorMatches (rowSelectorWires p)
      (6 * slot.val + copy.val) input = true) :
    RowDiagonalResultWithWorkRestorationSpec p (6 * slot.val + copy.val) true input
      ((rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  have result := rowDiagonalResultComputeUseUncomputeCircuit_correct p slot copy true true input clean
  simpa [diagonalBranchEnabled, selectorMatch] using result

/-- compact decoder の legal bit が 0 なら column 分岐は恒等である。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_illegal_identity
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot false presentValue input) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  apply columnDiagonalResultComputeUseUncomputeCircuit_inactive p slot copy false presentValue input clean
  simp [diagonalBranchEnabled]

/-- compact decoder の legal bit が 0 なら row 分岐は恒等である。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_illegal_identity
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot false presentValue input) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  apply rowDiagonalResultComputeUseUncomputeCircuit_inactive p slot copy false presentValue input clean
  simp [diagonalBranchEnabled]

/-- 対象 slot の present bit が 0 なら column 分岐は恒等である。 -/
theorem columnDiagonalResultComputeUseUncomputeCircuit_absent_identity
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue false input) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  apply columnDiagonalResultComputeUseUncomputeCircuit_inactive p slot copy legalValue false input clean
  simp [diagonalBranchEnabled]

/-- 対象 slot の present bit が 0 なら row 分岐は恒等である。 -/
theorem rowDiagonalResultComputeUseUncomputeCircuit_absent_identity
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue false input) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input := by
  apply rowDiagonalResultComputeUseUncomputeCircuit_inactive p slot copy legalValue false input clean
  simp [diagonalBranchEnabled]

end ReversibleCircuit

end ProbabilityGeneratorQProof
