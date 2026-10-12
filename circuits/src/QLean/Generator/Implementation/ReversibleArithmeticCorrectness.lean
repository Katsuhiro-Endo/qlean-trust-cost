import QLean.Generator.Implementation.SparseCircuitSemantics
import QLean.Generator.Implementation.QDecoderCircuit

/-!
# 可逆論理・算術部品の基底作用証明

各部品が保持するレジスタ値を`runBasis`上で証明する。証明はwire値だけを追跡し、
全計算基底や全体行列を列挙しない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 指定wire列が基底状態に持つbit値を同じ順序のリストとして読む。 -/
def readWires
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) : List Bool :=
  wires.map input

/-- 指定wire列がすべて1かを基底状態上で判定する。 -/
def allWiresTrue
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) : Bool :=
  (readWires wires input).all id

/-- 指定wire列がすべて0かを基底状態上で判定する。 -/
def allWiresFalse
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) : Bool :=
  (readWires wires input).all fun bit => !bit

/-- 一要素をリストの先頭から途中へ移す基本的な置換。 -/
theorem perm_cons_append {α : Type*} (value : α) (middle suffix : List α) :
    (value :: middle ++ suffix).Perm (middle ++ value :: suffix) := by
  exact List.perm_middle.symm

/--
重複のない`controls,target,remaining,scratches`配置から、AND回路順の
`controls,scratches,target`配置も重複なしと分かる。
-/
theorem nodup_controls_scratches_target
    {α : Type*} (controls remaining scratches : List α) (target : α)
    (layout : (controls ++ target :: remaining ++ scratches).Nodup) :
    (controls ++ scratches ++ [target]).Nodup := by
  have normalized : ((controls ++ target :: remaining) ++ scratches).Nodup := by
    simpa [List.append_assoc] using layout
  have prefixNodup := (List.nodup_append.mp normalized).1
  have scratchesNodup := (List.nodup_append.mp normalized).2.1
  have prefixScratchSeparated := (List.nodup_append.mp normalized).2.2
  have controlsNodup := (List.nodup_append.mp prefixNodup).1
  have controlsTailSeparated := (List.nodup_append.mp prefixNodup).2.2
  have controlsScratchesNodup : (controls ++ scratches).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨controlsNodup, scratchesNodup, ?_⟩
    intro control controlMember scratch scratchMember
    exact prefixScratchSeparated control
      (List.mem_append_left _ controlMember) scratch scratchMember
  apply List.nodup_append.mpr
  refine ⟨controlsScratchesNodup, by simp, ?_⟩
  intro wire wireMember finalTarget finalMember
  have finalTargetEqual : finalTarget = target := by simpa using finalMember
  subst finalTarget
  rcases List.mem_append.mp wireMember with controlMember | scratchMember
  · exact controlsTailSeparated wire controlMember target (by simp)
  · exact (prefixScratchSeparated target
      (List.mem_append_right controls (by simp)) wire scratchMember).symm

/-- CNOT基底作用は制御bitに応じてX作用または恒等作用になる。 -/
theorem cnotBasisAction_eq_conditional_x
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    cnotBasisAction control target input =
      if input control then xBasisAction target input else input := by
  funext wire
  by_cases enabled : input control <;>
    simp [cnotBasisAction, xBasisAction, enabled]

/-- 相異なる二標的へのX基底作用は可換である。 -/
theorem xBasisAction_commute
    {ancillaQubits systemQubits : Nat}
    (left right : Wire ancillaQubits systemQubits)
    (different : left ≠ right)
    (input : JointBasis ancillaQubits systemQubits) :
    xBasisAction left (xBasisAction right input) =
      xBasisAction right (xBasisAction left input) := by
  funext wire
  by_cases isLeft : wire = left <;> by_cases isRight : wire = right <;>
    simp [xBasisAction, different, different.symm, isLeft, isRight]

/--
作用wireがCNOTの制御・標的と異なれば、そのX作用とCNOT基底作用は可換である。
-/
theorem cnotBasisAction_x_commute
    {ancillaQubits systemQubits : Nat}
    (control target xTarget : Wire ancillaQubits systemQubits)
    (xDifferentControl : xTarget ≠ control)
    (xDifferentTarget : xTarget ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    cnotBasisAction control target (xBasisAction xTarget input) =
      xBasisAction xTarget (cnotBasisAction control target input) := by
  funext wire
  by_cases isXTarget : wire = xTarget <;> by_cases isCnotTarget : wire = target <;>
    cases controlValue : input control <;>
    simp [cnotBasisAction, xBasisAction, xDifferentControl.symm,
      xDifferentTarget, xDifferentTarget.symm,
      isXTarget, isCnotTarget, controlValue]

/-- Toffoliの標的を含まないwire列の読出し値はToffoli前後で変化しない。 -/
theorem readWires_toffoliBasisAction_of_not_mem
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ wires) :
    readWires wires (toffoliBasisAction control₁ control₂ target input) =
      readWires wires input := by
  apply List.map_congr_left
  intro wire member
  apply toffoliBasisAction_other
  intro equal
  subst wire
  exact targetAbsent member

/--
作用wireがToffoliの三wireと異なれば、そのX作用とToffoli基底作用は可換である。
-/
theorem toffoliBasisAction_x_commute
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target xTarget : Wire ancillaQubits systemQubits)
    (xDifferentFirst : xTarget ≠ control₁)
    (xDifferentSecond : xTarget ≠ control₂)
    (xDifferentTarget : xTarget ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    toffoliBasisAction control₁ control₂ target (xBasisAction xTarget input) =
      xBasisAction xTarget (toffoliBasisAction control₁ control₂ target input) := by
  funext wire
  by_cases isXTarget : wire = xTarget
  · subst wire
    cases firstValue : input control₁ <;> cases secondValue : input control₂ <;>
      simp [toffoliBasisAction, xBasisAction, xDifferentFirst.symm,
        xDifferentSecond.symm, xDifferentTarget, firstValue, secondValue]
  · by_cases isToffoliTarget : wire = target
    · subst wire
      cases firstValue : input control₁ <;> cases secondValue : input control₂ <;>
        simp [toffoliBasisAction, xBasisAction, xDifferentFirst.symm,
          xDifferentSecond.symm, xDifferentTarget.symm,
          firstValue, secondValue]
    · cases firstValue : input control₁ <;> cases secondValue : input control₂ <;>
        simp [toffoliBasisAction, xBasisAction, xDifferentFirst.symm,
          xDifferentSecond.symm, isXTarget,
          isToffoliTarget, firstValue, secondValue]

/--
既計算ANDと残りcontrolを延長する内部鎖は、clean scratchを消去しながら、全controlが
1のときだけtargetを反転する。
-/
theorem runBasis_andChainUse
    {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits)
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : controls.length ≤ scratches.length)
    (layoutNodup : (previous :: controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (andChainUse previous controls scratches target).runBasis
        reversibleGatePermutation input =
      if allWiresTrue (previous :: controls) input then
        xBasisAction target input
      else input := by
  induction controls generalizing previous scratches input with
  | nil =>
      have previousDifferentTarget : previous ≠ target := by
        intro equal
        apply (List.nodup_cons.mp layoutNodup).1
        simp [equal]
      rw [andChainUse]
      rw [runBasis_safeCnot previous target previousDifferentTarget]
      by_cases previousValue : input previous
      · rw [cnotBasisAction_eq_conditional_x, if_pos previousValue]
        simp [allWiresTrue, readWires, previousValue]
      · rw [cnotBasisAction_eq_conditional_x, if_neg previousValue]
        simp [allWiresTrue, readWires, previousValue]
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil => simp at enoughScratch
      | cons scratch scratches =>
          have previousFresh := (List.nodup_cons.mp layoutNodup).1
          have tailNodup := (List.nodup_cons.mp layoutNodup).2
          have controlFresh := (List.nodup_cons.mp tailNodup).1
          have remainingNodup := (List.nodup_cons.mp tailNodup).2
          have previousDifferentControl : previous ≠ control := by
            intro equal
            apply previousFresh
            simp [equal]
          have previousDifferentScratch : previous ≠ scratch := by
            intro equal
            apply previousFresh
            simp [equal]
          have controlDifferentScratch : control ≠ scratch := by
            intro equal
            apply controlFresh
            simp [equal]
          have targetDifferentPrevious : target ≠ previous := by
            intro equal
            apply previousFresh
            simp [equal]
          have targetDifferentControl : target ≠ control := by
            intro equal
            apply controlFresh
            simp [equal]
          have recursiveLayout :
              (scratch :: controls ++ scratches ++ [target]).Nodup := by
            have permutation := perm_cons_append scratch controls (scratches ++ [target])
            have reordered :
                (scratch :: controls ++ (scratches ++ [target])).Nodup := by
              apply permutation.symm.nodup
              simpa [List.append_assoc] using remainingNodup
            simpa [List.append_assoc] using reordered
          have scratchFresh := (List.nodup_cons.mp recursiveLayout).1
          have scratchZeroHead : input scratch = false := scratchZero scratch (by simp)
          let firstState := toffoliBasisAction previous control scratch input
          have controlsUnchanged :
              readWires controls firstState = readWires controls input := by
            exact readWires_toffoliBasisAction_of_not_mem controls previous control scratch
              input (by
                intro member
                exact scratchFresh (by simp [member]))
          have scratchesStillZero :
              ∀ wire ∈ scratches, firstState wire = false := by
            intro wire member
            dsimp [firstState]
            rw [toffoliBasisAction_other previous control scratch wire]
            · exact scratchZero wire (by simp [member])
            · intro equal
              apply scratchFresh
              rw [← equal]
              simp [member]
          have allControlsUnchanged :
              (List.map firstState controls).all id =
                (List.map input controls).all id := by
            simpa [readWires] using
              congrArg (fun values => values.all id) controlsUnchanged
          have recursiveCondition :
              allWiresTrue (scratch :: controls) firstState =
                allWiresTrue (previous :: control :: controls) input := by
            unfold allWiresTrue
            simp only [readWires, List.map_cons, List.all_cons]
            rw [allControlsUnchanged]
            simp only [id_eq]
            rw [show firstState scratch = (input previous && input control) by
              simp [firstState, scratchZeroHead]]
            exact Bool.and_assoc _ _ _
          have targetDifferentScratch : target ≠ scratch := by
            intro equal
            apply scratchFresh
            simp [equal]
          have tailEnough : controls.length ≤ scratches.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using enoughScratch
          rw [andChainUse, runBasis_seq,
            runBasis_safeToffoli previous control scratch previousDifferentControl
              previousDifferentScratch controlDifferentScratch,
            runBasis_seq]
          rw [inductionHypothesis scratch scratches firstState tailEnough recursiveLayout
            scratchesStillZero]
          rw [recursiveCondition]
          by_cases enabled : allWiresTrue (previous :: control :: controls) input
          · simp only [enabled, if_true]
            rw [runBasis_safeToffoli previous control scratch previousDifferentControl
              previousDifferentScratch controlDifferentScratch]
            rw [toffoliBasisAction_x_commute previous control scratch target
              targetDifferentPrevious targetDifferentControl targetDifferentScratch]
            simp [firstState, toffoliBasisAction_involutive previous control scratch
              previousDifferentControl previousDifferentScratch controlDifferentScratch]
          · simp only [enabled]
            rw [runBasis_safeToffoli previous control scratch previousDifferentControl
              previousDifferentScratch controlDifferentScratch]
            exact toffoliBasisAction_involutive previous control scratch
              previousDifferentControl previousDifferentScratch controlDifferentScratch input

/--
clean scratchと重複のないwire配置では、正制御多重Xは全controlが1のときだけtargetを
反転し、AND scratchをすべて入力値0へ戻す。
-/
theorem runBasis_positiveMultiControlledX
    {ancillaQubits systemQubits : Nat}
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (positiveMultiControlledX controls scratches target).runBasis
        reversibleGatePermutation input =
      if allWiresTrue controls input then xBasisAction target input else input := by
  cases controls with
  | nil =>
      simp [positiveMultiControlledX, allWiresTrue, readWires, runBasis_x]
  | cons control controls =>
      cases controls with
      | nil =>
          have controlDifferentTarget : control ≠ target := by
            intro equal
            have fresh := (List.nodup_cons.mp layoutNodup).1
            apply fresh
            simp [equal]
          rw [positiveMultiControlledX,
            runBasis_safeCnot control target controlDifferentTarget,
            cnotBasisAction_eq_conditional_x]
          simp [allWiresTrue, readWires]
      | cons control₂ controls =>
          cases scratches with
          | nil => simp at enoughScratch
          | cons scratch scratches =>
              have firstFresh := (List.nodup_cons.mp layoutNodup).1
              have afterFirstNodup := (List.nodup_cons.mp layoutNodup).2
              have secondFresh := (List.nodup_cons.mp afterFirstNodup).1
              have remainingNodup := (List.nodup_cons.mp afterFirstNodup).2
              have controlsDifferent : control ≠ control₂ := by
                intro equal
                apply firstFresh
                simp [equal]
              have firstDifferentScratch : control ≠ scratch := by
                intro equal
                apply firstFresh
                simp [equal]
              have secondDifferentScratch : control₂ ≠ scratch := by
                intro equal
                apply secondFresh
                simp [equal]
              have targetDifferentFirst : target ≠ control := by
                intro equal
                apply firstFresh
                simp [equal]
              have targetDifferentSecond : target ≠ control₂ := by
                intro equal
                apply secondFresh
                simp [equal]
              have recursiveLayout :
                  (scratch :: controls ++ scratches ++ [target]).Nodup := by
                have permutation :=
                  perm_cons_append scratch controls (scratches ++ [target])
                have reordered :
                    (scratch :: controls ++ (scratches ++ [target])).Nodup := by
                  apply permutation.symm.nodup
                  simpa [List.append_assoc] using remainingNodup
                simpa [List.append_assoc] using reordered
              have scratchFresh := (List.nodup_cons.mp recursiveLayout).1
              have scratchZeroHead : input scratch = false := scratchZero scratch (by simp)
              let firstState := toffoliBasisAction control control₂ scratch input
              have controlsUnchanged :
                  readWires controls firstState = readWires controls input := by
                exact readWires_toffoliBasisAction_of_not_mem controls control control₂
                  scratch input (by
                    intro member
                    exact scratchFresh (by simp [member]))
              have allControlsUnchanged :
                  (List.map firstState controls).all id =
                    (List.map input controls).all id := by
                simpa [readWires] using
                  congrArg (fun values => values.all id) controlsUnchanged
              have recursiveCondition :
                  allWiresTrue (scratch :: controls) firstState =
                    allWiresTrue (control :: control₂ :: controls) input := by
                unfold allWiresTrue
                simp only [readWires, List.map_cons, List.all_cons, id_eq]
                rw [allControlsUnchanged]
                rw [show firstState scratch = (input control && input control₂) by
                  simp [firstState, scratchZeroHead]]
                exact Bool.and_assoc _ _ _
              have scratchesStillZero :
                  ∀ wire ∈ scratches, firstState wire = false := by
                intro wire member
                dsimp [firstState]
                rw [toffoliBasisAction_other control control₂ scratch wire]
                · exact scratchZero wire (by simp [member])
                · intro equal
                  apply scratchFresh
                  rw [← equal]
                  simp [member]
              have targetDifferentScratch : target ≠ scratch := by
                intro equal
                apply scratchFresh
                simp [equal]
              have tailEnough : controls.length ≤ scratches.length := by
                simp only [List.length_cons] at enoughScratch
                omega
              rw [positiveMultiControlledX, runBasis_seq,
                runBasis_safeToffoli control control₂ scratch controlsDifferent
                  firstDifferentScratch secondDifferentScratch,
                runBasis_seq]
              rw [runBasis_andChainUse scratch controls scratches target firstState
                tailEnough recursiveLayout scratchesStillZero]
              rw [recursiveCondition]
              by_cases enabled :
                  allWiresTrue (control :: control₂ :: controls) input
              · simp only [enabled, if_true]
                rw [runBasis_safeToffoli control control₂ scratch controlsDifferent
                  firstDifferentScratch secondDifferentScratch]
                rw [toffoliBasisAction_x_commute control control₂ scratch target
                  targetDifferentFirst targetDifferentSecond targetDifferentScratch]
                simp [firstState, toffoliBasisAction_involutive control control₂ scratch
                  controlsDifferent firstDifferentScratch secondDifferentScratch]
              · simp only [enabled]
                rw [runBasis_safeToffoli control control₂ scratch controlsDifferent
                  firstDifferentScratch secondDifferentScratch]
                exact toffoliBasisAction_involutive control control₂ scratch
                  controlsDifferent firstDifferentScratch secondDifferentScratch input

/-- Bool値付き制御が現在の基底状態とすべて一致するかを判定する。 -/
def boolControlsSatisfied
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (input : JointBasis ancillaQubits systemQubits) : Bool :=
  controls.all fun control => decide (input control.1 = control.2)

/-- 全制御値を0に指定したBool条件は、対応wire列がすべて0という条件に等しい。 -/
theorem boolControlsSatisfied_allFalse
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    boolControlsSatisfied (wires.map fun wire => (wire, false)) input =
      allWiresFalse wires input := by
  induction wires with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      change
        (decide (input wire = false) &&
            boolControlsSatisfied (wires.map fun wire => (wire, false)) input) =
          (!input wire && allWiresFalse wires input)
      rw [inductionHypothesis]
      cases input wire <;> rfl

/-- 全wireを0指定条件へ写してからwire射影を取ると元のwire列へ戻る。 -/
@[simp] theorem map_false_controls_fst
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits)) :
    (wires.map fun wire => (wire, false)).map Prod.fst = wires := by
  induction wires with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp only [List.map_cons]
      rw [inductionHypothesis]

/-- 空の0-control反転列は恒等回路である。 -/
@[simp] theorem invertZeroControls_nil
    {ancillaQubits systemQubits : Nat} :
    invertZeroControls ([] : List (Wire ancillaQubits systemQubits × Bool)) =
      .identity := by
  rfl

/-- 期待値1の制御は0-control反転列へXを追加しない。 -/
@[simp] theorem invertZeroControls_cons_true
    {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits)
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    invertZeroControls ((wire, true) :: controls) =
      invertZeroControls controls := by
  rfl

/-- 期待値0の制御は先頭に一個のXを追加する。 -/
@[simp] theorem invertZeroControls_cons_false
    {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits)
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    invertZeroControls ((wire, false) :: controls) =
      .seq (.gate (.x wire)) (invertZeroControls controls) := by
  rfl

/-- 0-control反転列は、制御列に含まれないwireを変更しない。 -/
theorem runBasis_invertZeroControls_outside
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (outside : wire ∉ controls.map Prod.fst) :
    (invertZeroControls controls).runBasis reversibleGatePermutation input wire =
      input wire := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have wireDifferent : wire ≠ controlWire := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ controls.map Prod.fst := by
        intro member
        apply outside
        simp [member]
      cases expected with
      | false =>
          rw [invertZeroControls_cons_false, runBasis_seq, runBasis_local_x]
          rw [inductionHypothesis (xBasisAction controlWire input) tailOutside]
          exact xBasisAction_other controlWire wire wireDifferent input
      | true =>
          rw [invertZeroControls_cons_true]
          exact inductionHypothesis input tailOutside

/--
0-control反転列の後では、各制御wireは元の値が指定Boolと一致したかを表すbitになる。
-/
theorem runBasis_invertZeroControls_member
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (entry : Wire ancillaQubits systemQubits × Bool)
    (input : JointBasis ancillaQubits systemQubits)
    (controlNodup : (controls.map Prod.fst).Nodup)
    (member : entry ∈ controls) :
    (invertZeroControls controls).runBasis reversibleGatePermutation input entry.1 =
      decide (input entry.1 = entry.2) := by
  induction controls generalizing entry input with
  | nil => simp at member
  | cons head controls inductionHypothesis =>
      rcases head with ⟨headWire, headExpected⟩
      have headFresh := (List.nodup_cons.mp controlNodup).1
      have tailNodup := (List.nodup_cons.mp controlNodup).2
      by_cases isHead : entry = (headWire, headExpected)
      · subst entry
        have tailOutside : headWire ∉ controls.map Prod.fst := headFresh
        cases headExpected with
        | false =>
            rw [invertZeroControls_cons_false, runBasis_seq, runBasis_local_x]
            rw [runBasis_invertZeroControls_outside controls headWire
              (xBasisAction headWire input) tailOutside]
            cases value : input headWire <;> simp [value]
        | true =>
            rw [invertZeroControls_cons_true]
            rw [runBasis_invertZeroControls_outside controls headWire input tailOutside]
            cases input headWire <;> rfl
      · have tailMember : entry ∈ controls := by
          simpa [isHead] using member
        have entryDifferent : entry.1 ≠ headWire := by
          intro equal
          apply headFresh
          have mapped : entry.1 ∈ controls.map Prod.fst := by
            exact List.mem_map.mpr ⟨entry, tailMember, rfl⟩
          simpa [equal] using mapped
        cases headExpected with
        | false =>
            rw [invertZeroControls_cons_false, runBasis_seq, runBasis_local_x]
            rw [inductionHypothesis entry (xBasisAction headWire input)
              tailNodup tailMember]
            rw [xBasisAction_other headWire entry.1 entryDifferent]
        | true =>
            rw [invertZeroControls_cons_true]
            exact inductionHypothesis entry input tailNodup tailMember

/-- 0-control反転列は、列外のX作用と可換である。 -/
theorem runBasis_invertZeroControls_x_commute
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (xTarget : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetOutside : xTarget ∉ controls.map Prod.fst) :
    (invertZeroControls controls).runBasis reversibleGatePermutation
        (xBasisAction xTarget input) =
      xBasisAction xTarget
        ((invertZeroControls controls).runBasis reversibleGatePermutation input) := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have different : controlWire ≠ xTarget := by
        intro equal
        apply targetOutside
        simp [equal]
      have tailOutside : xTarget ∉ controls.map Prod.fst := by
        intro member
        apply targetOutside
        simp [member]
      cases expected with
      | false =>
          rw [invertZeroControls_cons_false, runBasis_seq, runBasis_local_x]
          rw [xBasisAction_commute controlWire xTarget different]
          exact inductionHypothesis (xBasisAction controlWire input) tailOutside
      | true =>
          rw [invertZeroControls_cons_true]
          exact inductionHypothesis input tailOutside

/-- 重複のない0-control反転列を二度作用させると元の基底状態へ戻る。 -/
theorem runBasis_invertZeroControls_involutive
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (input : JointBasis ancillaQubits systemQubits)
    (controlNodup : (controls.map Prod.fst).Nodup) :
    (invertZeroControls controls).runBasis reversibleGatePermutation
        ((invertZeroControls controls).runBasis reversibleGatePermutation input) =
      input := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have headFresh := (List.nodup_cons.mp controlNodup).1
      have tailNodup := (List.nodup_cons.mp controlNodup).2
      cases expected with
      | true =>
          rw [invertZeroControls_cons_true]
          exact inductionHypothesis input tailNodup
      | false =>
          simp only [invertZeroControls_cons_false, runBasis_seq, runBasis_x]
          rw [runBasis_invertZeroControls_x_commute controls controlWire
            ((invertZeroControls controls).runBasis reversibleGatePermutation
              (xBasisAction controlWire input)) headFresh]
          rw [inductionHypothesis (xBasisAction controlWire input) tailNodup]
          exact xBasisAction_involutive controlWire input

/-- 0-controlをXへ変換すると、正制御AND条件は元のBool付き条件と一致する。 -/
theorem allWiresTrue_invertZeroControls
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (input : JointBasis ancillaQubits systemQubits)
    (controlNodup : (controls.map Prod.fst).Nodup) :
    allWiresTrue (controls.map Prod.fst)
        ((invertZeroControls controls).runBasis reversibleGatePermutation input) =
      boolControlsSatisfied controls input := by
  unfold allWiresTrue readWires
  have values :
      (controls.map Prod.fst).map
          ((invertZeroControls controls).runBasis reversibleGatePermutation input) =
        controls.map (fun entry => decide (input entry.1 = entry.2)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry member
    exact runBasis_invertZeroControls_member controls entry input controlNodup member
  rw [values]
  simp [boolControlsSatisfied]

/--
Bool値付き多重制御Xは、指定条件がすべて成立するときだけtargetを反転し、scratchと
制御wireを入力値へ戻す。
-/
theorem runBasis_boolMultiControlledX
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (boolMultiControlledX controls scratches target).runBasis
        reversibleGatePermutation input =
      if boolControlsSatisfied controls input then
        xBasisAction target input
      else input := by
  let controlWires := controls.map Prod.fst
  let invert := invertZeroControls controls
  let prepared := invert.runBasis reversibleGatePermutation input
  have combinedNodup : (controlWires ++ scratches).Nodup := by
    exact (List.nodup_append.mp layoutNodup).1
  have controlNodup : controlWires.Nodup := by
    exact (List.nodup_append.mp combinedNodup).1
  have targetOutside : target ∉ controlWires := by
    intro member
    have separated := (List.nodup_append.mp layoutNodup).2.2
    exact separated target (List.mem_append_left scratches member)
      target (by simp) rfl
  have scratchesOutside : ∀ wire ∈ scratches, wire ∉ controlWires := by
    have separated := (List.nodup_append.mp combinedNodup).2.2
    intro wire scratchMember controlMember
    exact separated wire controlMember wire scratchMember rfl
  have preparedScratchZero : ∀ wire ∈ scratches, prepared wire = false := by
    intro wire member
    change (invertZeroControls controls).runBasis reversibleGatePermutation input wire =
      false
    rw [runBasis_invertZeroControls_outside controls wire input
      (scratchesOutside wire member)]
    exact scratchZero wire member
  have preparedCondition :
      allWiresTrue controlWires prepared = boolControlsSatisfied controls input := by
    exact allWiresTrue_invertZeroControls controls input controlNodup
  change invert.runBasis reversibleGatePermutation
      ((positiveMultiControlledX controlWires scratches target).runBasis
        reversibleGatePermutation prepared) = _
  rw [runBasis_positiveMultiControlledX controlWires scratches target prepared
    (by simpa [controlWires] using enoughScratch)
    (by simpa [controlWires] using layoutNodup) preparedScratchZero]
  rw [preparedCondition]
  by_cases enabled : boolControlsSatisfied controls input
  · simp only [enabled, if_true]
    rw [runBasis_invertZeroControls_x_commute controls target prepared targetOutside]
    rw [runBasis_invertZeroControls_involutive controls input controlNodup]
  · simp only [enabled]
    exact runBasis_invertZeroControls_involutive controls input controlNodup

/-- 制御wire外のX作用はBool値付き条件の真偽を変えない。 -/
theorem boolControlsSatisfied_x_outside
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetOutside : target ∉ controls.map Prod.fst) :
    boolControlsSatisfied controls (xBasisAction target input) =
      boolControlsSatisfied controls input := by
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have different : controlWire ≠ target := by
        intro equal
        apply targetOutside
        simp [equal]
      have tailOutside : target ∉ controls.map Prod.fst := by
        intro member
        apply targetOutside
        simp [member]
      simp only [boolControlsSatisfied, List.all_cons]
      rw [xBasisAction_other target controlWire different]
      congr 1
      simpa [boolControlsSatisfied] using inductionHypothesis tailOutside

/-- Bool制御列を順に適用したときのtarget反転parity。 -/
def boolControlProgramParity
    {ancillaQubits systemQubits : Nat} :
    List (List (Wire ancillaQubits systemQubits × Bool)) →
    JointBasis ancillaQubits systemQubits → Bool
  | [], _ => false
  | controls :: program, input =>
      if boolControlsSatisfied controls input then
        !(boolControlProgramParity program input)
      else
        boolControlProgramParity program input

/-- Bool列に含まれる`true`の個数を2で割ったparity。 -/
def boolParity : List Bool → Bool
  | [] => false
  | value :: values => if value then !(boolParity values) else boolParity values

/-- 制御programのparityは、各制御条件の真偽を並べたBool列のparityに等しい。 -/
theorem boolControlProgramParity_eq_boolParity
    {ancillaQubits systemQubits : Nat}
    (program : List (List (Wire ancillaQubits systemQubits × Bool)))
    (input : JointBasis ancillaQubits systemQubits) :
    boolControlProgramParity program input =
      boolParity (program.map fun controls => boolControlsSatisfied controls input) := by
  induction program with
  | nil => rfl
  | cons controls program inductionHypothesis =>
      simp only [boolControlProgramParity, List.map_cons, boolParity]
      rw [inductionHypothesis]

/--
little-endian二wordの各bit位置について、左0・右1かつ全上位bit一致という条件を並べる。
-/
def littleEndianLessConditions : List Bool → List Bool → List Bool → List Bool
  | leftBit :: left, rightBit :: right, equalities =>
      ((!leftBit) && rightBit && (equalities.drop 1).all id) ::
        littleEndianLessConditions left right (equalities.drop 1)
  | _, _, _ => []

/-- little-endian比較を、全bit位置の排他的な大小条件のparityとして定義する。 -/
def littleEndianLessBits (left right : List Bool) : Bool :=
  boolParity <| littleEndianLessConditions left right
    (List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit)) left right)

/-- little-endian Bool列を表す自然数へ変換する。 -/
def littleEndianNat : List Bool → Nat
  | [] => 0
  | bit :: bits => 2 * littleEndianNat bits + bit.toNat

/-- 各制御列の外側にあるXは、制御program全体の反転parityを変えない。 -/
theorem boolControlProgramParity_x_outside
    {ancillaQubits systemQubits : Nat}
    (program : List (List (Wire ancillaQubits systemQubits × Bool)))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetOutside : ∀ controls ∈ program, target ∉ controls.map Prod.fst) :
    boolControlProgramParity program (xBasisAction target input) =
      boolControlProgramParity program input := by
  induction program with
  | nil => rfl
  | cons controls program inductionHypothesis =>
      have headOutside := targetOutside controls (by simp)
      have tailOutside : ∀ tailControls ∈ program,
          target ∉ tailControls.map Prod.fst := by
        intro tailControls member
        exact targetOutside tailControls (by simp [member])
      simp only [boolControlProgramParity]
      rw [boolControlsSatisfied_x_outside controls target input headOutside]
      rw [inductionHypothesis tailOutside]

/-- Bool値付き多重制御Xを同じtargetへ順に適用する回路program。 -/
def boolControlProgram
    {ancillaQubits systemQubits : Nat}
    (program : List (List (Wire ancillaQubits systemQubits × Bool)))
    (scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| program.map fun controls =>
    boolMultiControlledX controls scratches target

/--
同じtargetへ作用するBool制御programは、各条件のparityが1のときだけtargetを反転し、
全scratchを0へ保つ。
-/
theorem runBasis_boolControlProgram
    {ancillaQubits systemQubits : Nat}
    (program : List (List (Wire ancillaQubits systemQubits × Bool)))
    (scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : ∀ controls ∈ program,
      controls.length ≤ scratches.length + 1)
    (layoutNodup : ∀ controls ∈ program,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (boolControlProgram program scratches target).runBasis
        reversibleGatePermutation input =
      if boolControlProgramParity program input then
        xBasisAction target input
      else input := by
  induction program generalizing input with
  | nil => rfl
  | cons controls program inductionHypothesis =>
      have headEnough := enoughScratch controls (by simp)
      have headLayout := layoutNodup controls (by simp)
      have tailEnough : ∀ tailControls ∈ program,
          tailControls.length ≤ scratches.length + 1 := by
        intro tailControls member
        exact enoughScratch tailControls (by simp [member])
      have tailLayout : ∀ tailControls ∈ program,
          (tailControls.map Prod.fst ++ scratches ++ [target]).Nodup := by
        intro tailControls member
        exact layoutNodup tailControls (by simp [member])
      have targetOutsideScratch : target ∉ scratches := by
        intro member
        have separated := (List.nodup_append.mp headLayout).2.2
        exact separated target (List.mem_append_right _ member)
          target (by simp) rfl
      have targetOutsideTailControls : ∀ tailControls ∈ program,
          target ∉ tailControls.map Prod.fst := by
        intro tailControls member targetMember
        have currentLayout := tailLayout tailControls member
        have separated := (List.nodup_append.mp currentLayout).2.2
        exact separated target (List.mem_append_left _ targetMember)
          target (by simp) rfl
      change (boolControlProgram program scratches target).runBasis
          reversibleGatePermutation
          ((boolMultiControlledX controls scratches target).runBasis
            reversibleGatePermutation input) = _
      rw [runBasis_boolMultiControlledX controls scratches target input
        headEnough headLayout scratchZero]
      by_cases enabled : boolControlsSatisfied controls input
      · simp only [enabled, if_true]
        have scratchZeroAfterX : ∀ wire ∈ scratches,
            xBasisAction target input wire = false := by
          intro wire member
          rw [xBasisAction_other target wire (by
            intro equal
            apply targetOutsideScratch
            simpa [equal] using member)]
          exact scratchZero wire member
        rw [inductionHypothesis (xBasisAction target input) tailEnough tailLayout
          scratchZeroAfterX]
        rw [boolControlProgramParity_x_outside program target input
          targetOutsideTailControls]
        cases parity : boolControlProgramParity program input <;>
          simp [boolControlProgramParity, enabled, parity,
            xBasisAction_involutive]
      · have disabled : boolControlsSatisfied controls input = false := by
          exact Bool.eq_false_of_not_eq_true enabled
        simp only [disabled, Bool.false_eq_true, if_false]
        rw [inductionHypothesis input tailEnough tailLayout scratchZero]
        simp [boolControlProgramParity, disabled]

/-- 二本のwire値を同時に交換する純粋な基底作用。 -/
def swapBasisAction
    {ancillaQubits systemQubits : Nat}
    (left right : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  fun wire =>
    if wire = left then input right
    else if wire = right then input left
    else input wire

/-- wire pair列を実行順に交換する純粋な基底作用。 -/
def swapPairsAction
    {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits × Wire ancillaQubits systemQubits) →
    JointBasis ancillaQubits systemQubits → JointBasis ancillaQubits systemQubits
  | [], input => input
  | pair :: pairs, input =>
      swapPairsAction pairs (swapBasisAction pair.1 pair.2 input)

/-- 交換対象外のwire値は一個のswap作用で変化しない。 -/
theorem swapBasisAction_other
    {ancillaQubits systemQubits : Nat}
    (left right wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (differentLeft : wire ≠ left) (differentRight : wire ≠ right) :
    swapBasisAction left right input wire = input wire := by
  simp [swapBasisAction, differentLeft, differentRight]

/-- 全pairの外側にあるwire値はpair交換列でも変化しない。 -/
theorem swapPairsAction_other
    {ancillaQubits systemQubits : Nat}
    (pairs : List
      (Wire ancillaQubits systemQubits × Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (outside : ∀ pair ∈ pairs, wire ≠ pair.1 ∧ wire ≠ pair.2) :
    swapPairsAction pairs input wire = input wire := by
  induction pairs generalizing input with
  | nil => rfl
  | cons pair pairs inductionHypothesis =>
      have headOutside := outside pair (by simp)
      have tailOutside : ∀ tailPair ∈ pairs,
          wire ≠ tailPair.1 ∧ wire ≠ tailPair.2 := by
        intro tailPair member
        exact outside tailPair (by simp [member])
      rw [swapPairsAction, inductionHypothesis _ tailOutside]
      exact swapBasisAction_other pair.1 pair.2 wire input
        headOutside.1 headOutside.2

/--
三基本ゲートへ分解したcontrolled swapは、controlが1なら二wireを交換し、0なら恒等に
なる。
-/
theorem runBasis_controlledSwapBit
    {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (controlDifferentLeft : control ≠ left)
    (controlDifferentRight : control ≠ right)
    (leftDifferentRight : left ≠ right) :
    (controlledSwapBit control left right).runBasis
        reversibleGatePermutation input =
      if input control then swapBasisAction left right input else input := by
  simp only [controlledSwapBit, runBasis_seq,
    runBasis_safeCnot left right leftDifferentRight,
    runBasis_safeToffoli control right left controlDifferentRight
      controlDifferentLeft leftDifferentRight.symm]
  funext wire
  by_cases isLeft : wire = left <;> by_cases isRight : wire = right <;>
    cases controlValue : input control <;>
    cases leftValue : input left <;> cases rightValue : input right <;>
    simp [cnotBasisAction, toffoliBasisAction, swapBasisAction,
      controlDifferentRight, leftDifferentRight,
      leftDifferentRight.symm, isLeft, isRight,
      controlValue, leftValue, rightValue]

/--
controlled swap列は、controlが1なら全pairを順に交換し、0なら恒等作用になる。
-/
theorem runBasis_controlledSwapPairs
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (pairs : List
      (Wire ancillaQubits systemQubits × Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (pairLayout : ∀ pair ∈ pairs,
      control ≠ pair.1 ∧ control ≠ pair.2 ∧ pair.1 ≠ pair.2) :
    (Circuit.sequence (pairs.map fun pair =>
      controlledSwapBit control pair.1 pair.2)).runBasis
        reversibleGatePermutation input =
      if input control then swapPairsAction pairs input else input := by
  induction pairs generalizing input with
  | nil =>
      simp [Circuit.sequence, swapPairsAction, Circuit.runBasis]
  | cons pair pairs inductionHypothesis =>
      have headLayout := pairLayout pair (by simp)
      have tailLayout : ∀ tailPair ∈ pairs,
          control ≠ tailPair.1 ∧ control ≠ tailPair.2 ∧
            tailPair.1 ≠ tailPair.2 := by
        intro tailPair member
        exact pairLayout tailPair (by simp [member])
      change (Circuit.sequence (pairs.map fun tailPair =>
          controlledSwapBit control tailPair.1 tailPair.2)).runBasis
          reversibleGatePermutation
          ((controlledSwapBit control pair.1 pair.2).runBasis
            reversibleGatePermutation input) = _
      rw [runBasis_controlledSwapBit control pair.1 pair.2 input
        headLayout.1 headLayout.2.1 headLayout.2.2]
      cases controlValue : input control with
      | false =>
          simpa [controlValue, swapPairsAction] using
            inductionHypothesis input tailLayout
      | true =>
          simp only [if_true]
          rw [inductionHypothesis (swapBasisAction pair.1 pair.2 input) tailLayout]
          rw [swapBasisAction_other pair.1 pair.2 control input
            headLayout.1 headLayout.2.1]
          simp [controlValue, swapPairsAction]

/-- controlled word swapの基底作用は対応bit pair列の条件付き交換に等しい。 -/
theorem runBasis_controlledSwapWord
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (pairLayout : ∀ pair ∈ left.zip right,
      control ≠ pair.1 ∧ control ≠ pair.2 ∧ pair.1 ≠ pair.2) :
    (controlledSwapWord control left right).runBasis
        reversibleGatePermutation input =
      if input control then swapPairsAction (left.zip right) input else input := by
  exact runBasis_controlledSwapPairs control (left.zip right) input pairLayout

/--
既知の下位wire列を制御として、上位側からincrement反転を適用する純粋な基底参照関数。
-/
def incrementWordCarrySequenceReference
    {ancillaQubits systemQubits : Nat}
    (lower : List (Wire ancillaQubits systemQubits)) :
    List (Wire ancillaQubits systemQubits) →
    JointBasis ancillaQubits systemQubits →
    JointBasis ancillaQubits systemQubits
  | [], input => input
  | target :: higher, input =>
      let higherState := incrementWordCarrySequenceReference (lower ++ [target]) higher input
      if allWiresTrue lower higherState then
        xBasisAction target higherState
      else
        higherState

/-- little-endian word全体を`2 ^ word.length`を法として1増やす純粋な基底参照関数。 -/
def incrementWordMod2PowInPlaceReference
    {ancillaQubits systemQubits : Nat}
    (word : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  incrementWordCarrySequenceReference [] word input

/-- carry入力付きlittle-endian incrementの純粋なBool列計算。 -/
def incrementBitsWithCarry : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits =>
      (if carry then !bit else bit) ::
        incrementBitsWithCarry (carry && bit) bits

/-- 通常の周期incrementは初期carryを1にしたBool列計算である。 -/
def incrementBits (bits : List Bool) : List Bool :=
  incrementBitsWithCarry true bits

/-- carry 0のincrementはBool列を変更しない。 -/
@[simp] theorem incrementBitsWithCarry_false (bits : List Bool) :
    incrementBitsWithCarry false bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp [incrementBitsWithCarry, inductionHypothesis]

/-- X標的を含まないwire列の読出し値はX作用前後で変化しない。 -/
theorem readWires_xBasisAction_of_not_mem
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ wires) :
    readWires wires (xBasisAction target input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  apply xBasisAction_other
  intro equal
  subst wire
  exact targetAbsent member

/-- increment参照関数は反転対象word外のwireを変更しない。 -/
theorem incrementWordCarrySequenceReference_outside
    {ancillaQubits systemQubits : Nat}
    (lower higher : List (Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (outside : wire ∉ higher) :
    incrementWordCarrySequenceReference lower higher input wire = input wire := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have wireDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ higher := by
        intro member
        apply outside
        simp [member]
      simp only [incrementWordCarrySequenceReference]
      let higherState := incrementWordCarrySequenceReference (lower ++ [target]) higher input
      have unchanged : higherState wire = input wire := by
        exact inductionHypothesis (lower ++ [target]) input tailOutside
      by_cases enabled : allWiresTrue lower higherState
      · rw [if_pos enabled]
        rw [xBasisAction_other target wire wireDifferent]
        exact unchanged
      · rw [if_neg enabled]
        exact unchanged

/--
重複のないword配置では、increment参照関数の読出し値はcarry付きBool incrementに
一致する。
-/
theorem readWires_incrementWordCarrySequenceReference
    {ancillaQubits systemQubits : Nat}
    (lower higher : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (layoutNodup : (lower ++ higher).Nodup) :
    readWires higher (incrementWordCarrySequenceReference lower higher input) =
      incrementBitsWithCarry (allWiresTrue lower input) (readWires higher input) := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have lowerNodup := (List.nodup_append.mp layoutNodup).1
      have targetTailNodup := (List.nodup_append.mp layoutNodup).2.1
      have lowerTailSeparated := (List.nodup_append.mp layoutNodup).2.2
      have targetFresh := (List.nodup_cons.mp targetTailNodup).1
      have recursiveLayout : ((lower ++ [target]) ++ higher).Nodup := by
        have prefixNodup : (lower ++ [target]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨lowerNodup, by simp, ?_⟩
          intro lowerWire lowerMember finalTarget finalMember
          have finalTargetEqual : finalTarget = target := by simpa using finalMember
          subst finalTarget
          exact lowerTailSeparated lowerWire lowerMember target (by simp)
        apply List.nodup_append.mpr
        refine ⟨prefixNodup, (List.nodup_cons.mp targetTailNodup).2, ?_⟩
        intro prefixWire prefixMember higherWire higherMember
        rcases List.mem_append.mp prefixMember with lowerMember | targetMember
        · exact lowerTailSeparated prefixWire lowerMember higherWire (by simp [higherMember])
        · have prefixEqual : prefixWire = target := by simpa using targetMember
          subst prefixWire
          intro equal
          apply targetFresh
          simpa [equal] using higherMember
      let higherState := incrementWordCarrySequenceReference (lower ++ [target]) higher input
      have targetUnchanged : higherState target = input target := by
        exact incrementWordCarrySequenceReference_outside (lower ++ [target]) higher target input targetFresh
      have lowerUnchanged : readWires lower higherState = readWires lower input := by
        apply List.map_congr_left
        intro wire member
        apply incrementWordCarrySequenceReference_outside (lower ++ [target]) higher wire input
        intro higherMember
        exact lowerTailSeparated wire member wire (by simp [higherMember]) rfl
      have conditionUnchanged :
          allWiresTrue lower higherState = allWiresTrue lower input := by
        unfold allWiresTrue
        simpa [readWires] using congrArg (fun values => values.all id) lowerUnchanged
      have tailResult : readWires higher higherState =
          incrementBitsWithCarry (allWiresTrue (lower ++ [target]) input)
            (readWires higher input) := by
        exact inductionHypothesis (lower ++ [target]) input recursiveLayout
      have extendedCarry :
          allWiresTrue (lower ++ [target]) input =
            (allWiresTrue lower input && input target) := by
        simp [allWiresTrue, readWires, List.all_append]
      simp only [incrementWordCarrySequenceReference, readWires, List.map_cons]
      rw [conditionUnchanged]
      by_cases carry : allWiresTrue lower input
      · simp only [carry, if_true, incrementBitsWithCarry, Bool.true_and]
        congr 1
        · calc
            xBasisAction target higherState target = !higherState target :=
              xBasisAction_target target higherState
            _ = !input target := congrArg (fun value => !value) targetUnchanged
        · change readWires higher (xBasisAction target higherState) =
            incrementBitsWithCarry (input target) (readWires higher input)
          rw [readWires_xBasisAction_of_not_mem higher target higherState targetFresh]
          rw [tailResult, extendedCarry, carry]
          rfl
      · have carryFalse : allWiresTrue lower input = false :=
          Bool.eq_false_of_not_eq_true carry
        simp only [carryFalse, Bool.false_eq_true, if_false,
          incrementBitsWithCarry, Bool.false_and, incrementBitsWithCarry_false]
        congr 1
        change readWires higher higherState = readWires higher input
        rw [tailResult, extendedCarry, carryFalse]
        simp

/--
重複のないclean layoutでは、再帰的increment正本回路の基底作用は
`incrementWordCarrySequenceReference`に一致し、scratchを変更しない。
-/
theorem runBasis_incrementWordCarrySequenceCircuit
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (incrementWordCarrySequenceCircuit lower higher scratches).runBasis
        reversibleGatePermutation input =
      incrementWordCarrySequenceReference lower higher input := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ higher).length ≤ scratches.length + 2 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          ((lower ++ [target]) ++ higher ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      rw [incrementWordCarrySequenceCircuit, runBasis_seq]
      rw [inductionHypothesis (lower ++ [target]) input recursiveEnough
        recursiveLayout scratchZero]
      let higherState := incrementWordCarrySequenceReference (lower ++ [target]) higher input
      have normalized : ((lower ++ target :: higher) ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      have targetScratchLayout : (lower ++ scratches ++ [target]).Nodup := by
        exact nodup_controls_scratches_target lower higher scratches target layoutNodup
      have stageEnough : lower.length ≤ scratches.length + 1 := by
        simp only [List.length_append, List.length_cons] at enoughScratch
        omega
      have higherStateScratchZero : ∀ wire ∈ scratches,
          higherState wire = false := by
        have separated := (List.nodup_append.mp normalized).2.2
        intro wire scratchMember
        change incrementWordCarrySequenceReference (lower ++ [target]) higher input wire = false
        rw [incrementWordCarrySequenceReference_outside (lower ++ [target]) higher wire input (by
          intro higherMember
          exact separated wire
            (List.mem_append_right lower (by simp [higherMember]))
            wire scratchMember rfl)]
        exact scratchZero wire scratchMember
      rw [runBasis_positiveMultiControlledX lower scratches target higherState
        stageEnough targetScratchLayout higherStateScratchZero]
      rfl

/-- clean layout上の周期increment回路は空の下位制御から参照関数を実行する。 -/
theorem runBasis_incrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (incrementWordMod2PowInPlaceCircuit word scratches).runBasis
        reversibleGatePermutation input =
      incrementWordMod2PowInPlaceReference word input := by
  simpa [incrementWordMod2PowInPlaceCircuit, incrementWordMod2PowInPlaceReference] using
    runBasis_incrementWordCarrySequenceCircuit [] word scratches input
      (by simpa using enoughScratch) (by simpa using layoutNodup) scratchZero

/-- 周期increment回路後のword読出し値は純粋な`incrementBits`に一致する。 -/
theorem readWires_incrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    readWires word
        ((incrementWordMod2PowInPlaceCircuit word scratches).runBasis
          reversibleGatePermutation input) =
      incrementBits (readWires word input) := by
  rw [runBasis_incrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
    layoutNodup scratchZero]
  have wordNodup := (List.nodup_append.mp layoutNodup).1
  simpa [incrementWordMod2PowInPlaceReference, incrementBits, allWiresTrue, readWires] using
    readWires_incrementWordCarrySequenceReference [] word input (by simpa using wordNodup)

/--
既知の下位wire列を0制御として、上位側からdecrement反転を適用する純粋な基底参照関数。
-/
def decrementWordBorrowSequenceReference
    {ancillaQubits systemQubits : Nat}
    (lower : List (Wire ancillaQubits systemQubits)) :
    List (Wire ancillaQubits systemQubits) →
    JointBasis ancillaQubits systemQubits →
    JointBasis ancillaQubits systemQubits
  | [], input => input
  | target :: higher, input =>
      let higherState := decrementWordBorrowSequenceReference (lower ++ [target]) higher input
      if allWiresFalse lower higherState then
        xBasisAction target higherState
      else
        higherState

/-- little-endian word全体を`2 ^ word.length`を法として1減らす純粋な基底参照関数。 -/
def decrementWordMod2PowInPlaceReference
    {ancillaQubits systemQubits : Nat}
    (word : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  decrementWordBorrowSequenceReference [] word input

/-- borrow入力付きlittle-endian decrementの純粋なBool列計算。 -/
def decrementBitsWithBorrow : Bool → List Bool → List Bool
  | _, [] => []
  | borrow, bit :: bits =>
      (if borrow then !bit else bit) ::
        decrementBitsWithBorrow (borrow && !bit) bits

/-- 通常の周期decrementは初期borrowを1にしたBool列計算である。 -/
def decrementBits (bits : List Bool) : List Bool :=
  decrementBitsWithBorrow true bits

/-- borrow 0のdecrementはBool列を変更しない。 -/
@[simp] theorem decrementBitsWithBorrow_false (bits : List Bool) :
    decrementBitsWithBorrow false bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp [decrementBitsWithBorrow, inductionHypothesis]

/-- decrement参照関数は反転対象word外のwireを変更しない。 -/
theorem decrementWordBorrowSequenceReference_outside
    {ancillaQubits systemQubits : Nat}
    (lower higher : List (Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (outside : wire ∉ higher) :
    decrementWordBorrowSequenceReference lower higher input wire = input wire := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have wireDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ higher := by
        intro member
        apply outside
        simp [member]
      simp only [decrementWordBorrowSequenceReference]
      let higherState := decrementWordBorrowSequenceReference (lower ++ [target]) higher input
      have unchanged : higherState wire = input wire := by
        exact inductionHypothesis (lower ++ [target]) input tailOutside
      by_cases enabled : allWiresFalse lower higherState
      · rw [if_pos enabled]
        rw [xBasisAction_other target wire wireDifferent]
        exact unchanged
      · rw [if_neg enabled]
        exact unchanged

/--
重複のないword配置では、decrement参照関数の読出し値はborrow付きBool decrementに
一致する。
-/
theorem readWires_decrementWordBorrowSequenceReference
    {ancillaQubits systemQubits : Nat}
    (lower higher : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (layoutNodup : (lower ++ higher).Nodup) :
    readWires higher (decrementWordBorrowSequenceReference lower higher input) =
      decrementBitsWithBorrow (allWiresFalse lower input)
        (readWires higher input) := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have lowerNodup := (List.nodup_append.mp layoutNodup).1
      have targetTailNodup := (List.nodup_append.mp layoutNodup).2.1
      have lowerTailSeparated := (List.nodup_append.mp layoutNodup).2.2
      have targetFresh := (List.nodup_cons.mp targetTailNodup).1
      have recursiveLayout : ((lower ++ [target]) ++ higher).Nodup := by
        have prefixNodup : (lower ++ [target]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨lowerNodup, by simp, ?_⟩
          intro lowerWire lowerMember finalTarget finalMember
          have finalTargetEqual : finalTarget = target := by simpa using finalMember
          subst finalTarget
          exact lowerTailSeparated lowerWire lowerMember target (by simp)
        apply List.nodup_append.mpr
        refine ⟨prefixNodup, (List.nodup_cons.mp targetTailNodup).2, ?_⟩
        intro prefixWire prefixMember higherWire higherMember
        rcases List.mem_append.mp prefixMember with lowerMember | targetMember
        · exact lowerTailSeparated prefixWire lowerMember higherWire (by simp [higherMember])
        · have prefixEqual : prefixWire = target := by simpa using targetMember
          subst prefixWire
          intro equal
          apply targetFresh
          simpa [equal] using higherMember
      let higherState := decrementWordBorrowSequenceReference (lower ++ [target]) higher input
      have targetUnchanged : higherState target = input target := by
        exact decrementWordBorrowSequenceReference_outside (lower ++ [target]) higher target input targetFresh
      have lowerUnchanged : readWires lower higherState = readWires lower input := by
        apply List.map_congr_left
        intro wire member
        apply decrementWordBorrowSequenceReference_outside (lower ++ [target]) higher wire input
        intro higherMember
        exact lowerTailSeparated wire member wire (by simp [higherMember]) rfl
      have conditionUnchanged :
          allWiresFalse lower higherState = allWiresFalse lower input := by
        unfold allWiresFalse
        simpa [readWires] using congrArg (fun values => values.all fun bit => !bit)
          lowerUnchanged
      have tailResult : readWires higher higherState =
          decrementBitsWithBorrow (allWiresFalse (lower ++ [target]) input)
            (readWires higher input) := by
        exact inductionHypothesis (lower ++ [target]) input recursiveLayout
      have extendedBorrow :
          allWiresFalse (lower ++ [target]) input =
            (allWiresFalse lower input && !input target) := by
        simp [allWiresFalse, readWires, List.all_append]
      simp only [decrementWordBorrowSequenceReference, readWires, List.map_cons]
      rw [conditionUnchanged]
      by_cases borrow : allWiresFalse lower input
      · simp only [borrow, if_true, decrementBitsWithBorrow, Bool.true_and]
        congr 1
        · calc
            xBasisAction target higherState target = !higherState target :=
              xBasisAction_target target higherState
            _ = !input target := congrArg (fun value => !value) targetUnchanged
        · change readWires higher (xBasisAction target higherState) =
            decrementBitsWithBorrow (!input target) (readWires higher input)
          rw [readWires_xBasisAction_of_not_mem higher target higherState targetFresh]
          rw [tailResult, extendedBorrow, borrow]
          rfl
      · have borrowFalse : allWiresFalse lower input = false :=
          Bool.eq_false_of_not_eq_true borrow
        simp only [borrowFalse, Bool.false_eq_true, if_false,
          decrementBitsWithBorrow, Bool.false_and, decrementBitsWithBorrow_false]
        congr 1
        change readWires higher higherState = readWires higher input
        rw [tailResult, extendedBorrow, borrowFalse]
        simp

/--
重複のないclean layoutでは、再帰的decrement正本回路の基底作用は
`decrementWordBorrowSequenceReference`に一致し、scratchを変更しない。
-/
theorem runBasis_decrementWordBorrowSequenceCircuit
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (decrementWordBorrowSequenceCircuit lower higher scratches).runBasis
        reversibleGatePermutation input =
      decrementWordBorrowSequenceReference lower higher input := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ higher).length ≤ scratches.length + 2 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          ((lower ++ [target]) ++ higher ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      rw [decrementWordBorrowSequenceCircuit, runBasis_seq]
      rw [inductionHypothesis (lower ++ [target]) input recursiveEnough
        recursiveLayout scratchZero]
      let higherState := decrementWordBorrowSequenceReference (lower ++ [target]) higher input
      have normalized : ((lower ++ target :: higher) ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      have targetScratchLayout :
          ((lower.map fun wire => (wire, false)).map Prod.fst ++
            scratches ++ [target]).Nodup := by
        rw [map_false_controls_fst]
        exact nodup_controls_scratches_target lower higher scratches target layoutNodup
      have stageEnough : lower.length ≤ scratches.length + 1 := by
        simp only [List.length_append, List.length_cons] at enoughScratch
        omega
      have higherStateScratchZero : ∀ wire ∈ scratches,
          higherState wire = false := by
        have separated := (List.nodup_append.mp normalized).2.2
        intro wire scratchMember
        change decrementWordBorrowSequenceReference (lower ++ [target]) higher input wire = false
        rw [decrementWordBorrowSequenceReference_outside (lower ++ [target]) higher wire input (by
          intro higherMember
          exact separated wire
            (List.mem_append_right lower (by simp [higherMember]))
            wire scratchMember rfl)]
        exact scratchZero wire scratchMember
      rw [runBasis_boolMultiControlledX
        (lower.map fun wire => (wire, false)) scratches target higherState
        (by simpa using stageEnough) targetScratchLayout higherStateScratchZero]
      rw [boolControlsSatisfied_allFalse lower higherState]
      rfl

/-- clean layout上の周期decrement回路は空の下位制御から参照関数を実行する。 -/
theorem runBasis_decrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (decrementWordMod2PowInPlaceCircuit word scratches).runBasis
        reversibleGatePermutation input =
      decrementWordMod2PowInPlaceReference word input := by
  simpa [decrementWordMod2PowInPlaceCircuit, decrementWordMod2PowInPlaceReference] using
    runBasis_decrementWordBorrowSequenceCircuit [] word scratches input
      (by simpa using enoughScratch) (by simpa using layoutNodup) scratchZero

/-- 周期decrement回路後のword読出し値は純粋な`decrementBits`に一致する。 -/
theorem readWires_decrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    readWires word
        ((decrementWordMod2PowInPlaceCircuit word scratches).runBasis
          reversibleGatePermutation input) =
      decrementBits (readWires word input) := by
  rw [runBasis_decrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
    layoutNodup scratchZero]
  have wordNodup := (List.nodup_append.mp layoutNodup).1
  simpa [decrementWordMod2PowInPlaceReference, decrementBits, allWiresFalse, readWires] using
    readWires_decrementWordBorrowSequenceReference [] word input (by simpa using wordNodup)

/-- CNOT標的を含まないwire列の読出し値はCNOT前後で変化しない。 -/
theorem readWires_cnotBasisAction_of_not_mem
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (control target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ wires) :
    readWires wires (cnotBasisAction control target input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  apply cnotBasisAction_other
  intro equal
  subst wire
  exact targetAbsent member

/-- 一bit等値回路の出力flagは、二入力bitが等しいときちょうど1になる。 -/
theorem runBasis_computeBitEqual_flag
    {ancillaQubits systemQubits : Nat}
    (left right flag : Wire ancillaQubits systemQubits)
    (leftDifferent : left ≠ flag)
    (rightDifferent : right ≠ flag)
    (input : JointBasis ancillaQubits systemQubits)
    (flagZero : input flag = false) :
    (computeBitEqual left right flag).runBasis reversibleGatePermutation input flag =
      decide (input left = input right) := by
  simp only [computeBitEqual, runBasis_seq,
    runBasis_safeCnot left flag leftDifferent,
    runBasis_safeCnot right flag rightDifferent, runBasis_x]
  by_cases sameInputs : input left = input right
  · simp [sameInputs, flagZero, cnotBasisAction, xBasisAction, rightDifferent]
  · cases leftValue : input left <;> cases rightValue : input right <;>
      simp_all [cnotBasisAction, xBasisAction]

/-- 一bit等値回路はflag以外の全wireを変更しない。 -/
theorem runBasis_computeBitEqual_other
    {ancillaQubits systemQubits : Nat}
    (left right flag wire : Wire ancillaQubits systemQubits)
    (leftDifferent : left ≠ flag)
    (rightDifferent : right ≠ flag)
    (wireDifferent : wire ≠ flag)
    (input : JointBasis ancillaQubits systemQubits) :
    (computeBitEqual left right flag).runBasis reversibleGatePermutation input wire =
      input wire := by
  simp only [computeBitEqual, runBasis_seq,
    runBasis_safeCnot left flag leftDifferent,
    runBasis_safeCnot right flag rightDifferent, runBasis_x]
  simp [cnotBasisAction, xBasisAction, wireDifferent]

/-- 等値flag計算は、二入力とflagの外にあるwireへのX作用と可換である。 -/
theorem runBasis_computeBitEqual_x_commute
    {ancillaQubits systemQubits : Nat}
    (left right flag xTarget : Wire ancillaQubits systemQubits)
    (leftDifferentFlag : left ≠ flag)
    (rightDifferentFlag : right ≠ flag)
    (xDifferentLeft : xTarget ≠ left)
    (xDifferentRight : xTarget ≠ right)
    (xDifferentFlag : xTarget ≠ flag)
    (input : JointBasis ancillaQubits systemQubits) :
    (computeBitEqual left right flag).runBasis reversibleGatePermutation
        (xBasisAction xTarget input) =
      xBasisAction xTarget
        ((computeBitEqual left right flag).runBasis reversibleGatePermutation input) := by
  simp only [computeBitEqual, runBasis_seq,
    runBasis_safeCnot left flag leftDifferentFlag,
    runBasis_safeCnot right flag rightDifferentFlag, runBasis_x]
  rw [cnotBasisAction_x_commute left flag xTarget xDifferentLeft xDifferentFlag]
  rw [cnotBasisAction_x_commute right flag xTarget xDifferentRight xDifferentFlag]
  rw [xBasisAction_commute flag xTarget xDifferentFlag.symm]

/-- 等値flag列の一括計算も、全入力・flag外のwireへのX作用と可換である。 -/
theorem runBasis_computeEqualityFlags_x_commute
    {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits))
    (xTarget : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftDisjoint : left.Disjoint flags)
    (rightDisjoint : right.Disjoint flags)
    (xAbsentLeft : xTarget ∉ left)
    (xAbsentRight : xTarget ∉ right)
    (xAbsentFlags : xTarget ∉ flags) :
    (computeEqualityFlags left right flags).runBasis reversibleGatePermutation
        (xBasisAction xTarget input) =
      xBasisAction xTarget
        ((computeEqualityFlags left right flags).runBasis
          reversibleGatePermutation input) := by
  induction left generalizing right flags input with
  | nil =>
      simp [computeEqualityFlags, Circuit.sequence, Circuit.runBasis]
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil =>
          simp [computeEqualityFlags, Circuit.sequence, Circuit.runBasis]
      | cons rightHead rightTail =>
          cases flags with
          | nil =>
              simp [computeEqualityFlags, Circuit.sequence, Circuit.runBasis]
          | cons flagHead flagTail =>
              rcases List.disjoint_cons_right.mp leftDisjoint with
                ⟨flagHeadAbsentLeft, leftDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp leftDisjointTailFlags with
                ⟨leftHeadAbsentFlagTail, leftTailDisjoint⟩
              rcases List.disjoint_cons_right.mp rightDisjoint with
                ⟨flagHeadAbsentRight, rightDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp rightDisjointTailFlags with
                ⟨rightHeadAbsentFlagTail, rightTailDisjoint⟩
              have leftDifferentFlag : leftHead ≠ flagHead := by
                intro equal
                subst leftHead
                exact flagHeadAbsentLeft (by simp)
              have rightDifferentFlag : rightHead ≠ flagHead := by
                intro equal
                subst rightHead
                exact flagHeadAbsentRight (by simp)
              have xPartsLeft : xTarget ≠ leftHead ∧ xTarget ∉ leftTail := by
                simpa only [List.mem_cons, not_or] using xAbsentLeft
              have xPartsRight : xTarget ≠ rightHead ∧ xTarget ∉ rightTail := by
                simpa only [List.mem_cons, not_or] using xAbsentRight
              have xPartsFlags : xTarget ≠ flagHead ∧ xTarget ∉ flagTail := by
                simpa only [List.mem_cons, not_or] using xAbsentFlags
              change (Circuit.seq (computeBitEqual leftHead rightHead flagHead)
                (computeEqualityFlags leftTail rightTail flagTail)).runBasis
                  reversibleGatePermutation (xBasisAction xTarget input) = _
              rw [runBasis_core_seq]
              simp only [runBasis_core_eq_local]
              rw [runBasis_computeBitEqual_x_commute leftHead rightHead
                flagHead xTarget leftDifferentFlag rightDifferentFlag
                xPartsLeft.1 xPartsRight.1 xPartsFlags.1]
              rw [inductionHypothesis rightTail flagTail _ leftTailDisjoint
                rightTailDisjoint xPartsLeft.2 xPartsRight.2 xPartsFlags.2]
              rfl

/-- 等値flag列の一括計算はflag列に含まれないwireを変更しない。 -/
theorem runBasis_computeEqualityFlags_outside
    {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftDisjoint : left.Disjoint flags)
    (rightDisjoint : right.Disjoint flags)
    (outside : wire ∉ flags) :
    (computeEqualityFlags left right flags).runBasis reversibleGatePermutation input wire =
      input wire := by
  induction left generalizing right flags input with
  | nil =>
      simp [computeEqualityFlags, Circuit.sequence, Circuit.runBasis]
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil =>
          simp [computeEqualityFlags, Circuit.sequence, Circuit.runBasis]
      | cons rightHead rightTail =>
          cases flags with
          | nil =>
              simp [computeEqualityFlags, Circuit.sequence, Circuit.runBasis]
          | cons flagHead flagTail =>
              rcases List.disjoint_cons_right.mp leftDisjoint with
                ⟨flagHeadAbsentLeft, leftDisjointTailFlags⟩
              rcases List.disjoint_cons_right.mp rightDisjoint with
                ⟨flagHeadAbsentRight, rightDisjointTailFlags⟩
              have leftTailDisjoint : leftTail.Disjoint flagTail :=
                (List.disjoint_cons_left.mp leftDisjointTailFlags).2
              have rightTailDisjoint : rightTail.Disjoint flagTail :=
                (List.disjoint_cons_left.mp rightDisjointTailFlags).2
              have leftDifferent : leftHead ≠ flagHead := by
                intro equal
                subst leftHead
                exact flagHeadAbsentLeft (by simp)
              have rightDifferent : rightHead ≠ flagHead := by
                intro equal
                subst rightHead
                exact flagHeadAbsentRight (by simp)
              have outsideParts : wire ≠ flagHead ∧ wire ∉ flagTail := by
                simpa only [List.mem_cons, not_or] using outside
              change (Circuit.seq (computeBitEqual leftHead rightHead flagHead)
                (computeEqualityFlags leftTail rightTail flagTail)).runBasis
                  reversibleGatePermutation input wire = input wire
              rw [runBasis_core_seq]
              simp only [runBasis_core_eq_local]
              rw [inductionHypothesis rightTail flagTail _ leftTailDisjoint
                rightTailDisjoint outsideParts.2]
              exact runBasis_computeBitEqual_other leftHead rightHead flagHead wire
                leftDifferent rightDifferent outsideParts.1 input

/--
相異なるclean flag列へbitごとの等値を計算すると、各flagは対応入力bitの一致判定になる。
入力列とflag列の長さだけで帰納し、word値は列挙しない。
-/
theorem runBasis_computeEqualityFlags_readWires
    {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = flags.length)
    (rightLength : right.length = flags.length)
    (leftDisjoint : left.Disjoint flags)
    (rightDisjoint : right.Disjoint flags)
    (flagsNodup : flags.Nodup)
    (flagsZero : readWires flags input = List.replicate flags.length false) :
    readWires flags
        ((computeEqualityFlags left right flags).runBasis
          reversibleGatePermutation input) =
      List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
        (readWires left input) (readWires right input) := by
  induction left generalizing right flags input with
  | nil =>
      have flagsEmpty : flags = [] := by
        cases flags with
        | nil => rfl
        | cons flagHead flagTail => simp at leftLength
      subst flags
      have rightEmpty : right = [] := by
        cases right with
        | nil => rfl
        | cons rightHead rightTail => simp at rightLength
      subst right
      rfl
  | cons leftHead leftTail inductionHypothesis =>
      cases flags with
      | nil => simp at leftLength
      | cons flagHead flagTail =>
          cases right with
          | nil => simp at rightLength
          | cons rightHead rightTail =>
              have leftTailLength : leftTail.length = flagTail.length := by
                simpa using Nat.succ.inj leftLength
              have rightTailLength : rightTail.length = flagTail.length := by
                simpa using Nat.succ.inj rightLength
              rcases List.disjoint_cons_right.mp leftDisjoint with
                ⟨flagHeadAbsentLeft, leftDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp leftDisjointTailFlags with
                ⟨leftHeadAbsentFlagTail, leftTailDisjoint⟩
              rcases List.disjoint_cons_right.mp rightDisjoint with
                ⟨flagHeadAbsentRight, rightDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp rightDisjointTailFlags with
                ⟨rightHeadAbsentFlagTail, rightTailDisjoint⟩
              have leftDifferent : leftHead ≠ flagHead := by
                intro equal
                subst leftHead
                exact flagHeadAbsentLeft (by simp)
              have rightDifferent : rightHead ≠ flagHead := by
                intro equal
                subst rightHead
                exact flagHeadAbsentRight (by simp)
              have flagHeadAbsentTail : flagHead ∉ flagTail :=
                (List.nodup_cons.mp flagsNodup).1
              have flagTailNodup : flagTail.Nodup :=
                (List.nodup_cons.mp flagsNodup).2
              have flagHeadZero : input flagHead = false := by
                have headEquality := congrArg List.head? flagsZero
                simpa [readWires, List.replicate_succ, ← Nat.succ_eq_add_one]
                  using headEquality
              have flagTailZero :
                  readWires flagTail input = List.replicate flagTail.length false := by
                have tailEquality := congrArg List.tail flagsZero
                simpa [readWires] using tailEquality
              let firstState :=
                (computeBitEqual leftHead rightHead flagHead).runBasis
                  reversibleGatePermutation input
              have leftTailUnchanged : readWires leftTail firstState = readWires leftTail input := by
                apply List.map_congr_left
                intro wire member
                exact runBasis_computeBitEqual_other leftHead rightHead flagHead wire
                  leftDifferent rightDifferent
                  (by
                    intro equal
                    apply flagHeadAbsentLeft
                    rw [← equal]
                    exact List.mem_cons_of_mem leftHead member) input
              have rightTailUnchanged :
                  readWires rightTail firstState = readWires rightTail input := by
                apply List.map_congr_left
                intro wire member
                exact runBasis_computeBitEqual_other leftHead rightHead flagHead wire
                  leftDifferent rightDifferent
                  (by
                    intro equal
                    apply flagHeadAbsentRight
                    rw [← equal]
                    exact List.mem_cons_of_mem rightHead member) input
              have flagTailStillZero :
                  readWires flagTail firstState = List.replicate flagTail.length false := by
                rw [show readWires flagTail firstState = readWires flagTail input by
                  apply List.map_congr_left
                  intro wire member
                  exact runBasis_computeBitEqual_other leftHead rightHead flagHead wire
                    leftDifferent rightDifferent
                    (by
                      intro equal
                      apply flagHeadAbsentTail
                      rw [← equal]
                      exact member) input]
                exact flagTailZero
              have tailResult := inductionHypothesis rightTail flagTail firstState
                leftTailLength rightTailLength leftTailDisjoint rightTailDisjoint
                flagTailNodup flagTailStillZero
              change readWires (flagHead :: flagTail)
                  ((Circuit.seq (computeBitEqual leftHead rightHead flagHead)
                    (computeEqualityFlags leftTail rightTail flagTail)).runBasis
                      reversibleGatePermutation input) = _
              rw [runBasis_core_seq]
              simp only [runBasis_core_eq_local]
              simp only [readWires, List.map_cons, List.zipWith_cons_cons]
              congr 1
              · rw [runBasis_computeEqualityFlags_outside leftTail rightTail flagTail
                  flagHead firstState leftTailDisjoint rightTailDisjoint
                  flagHeadAbsentTail]
                exact runBasis_computeBitEqual_flag leftHead rightHead flagHead
                  leftDifferent rightDifferent input flagHeadZero
              · change readWires flagTail
                    ((computeEqualityFlags leftTail rightTail flagTail).runBasis
                      reversibleGatePermutation firstState) = _
                rw [tailResult, leftTailUnchanged, rightTailUnchanged]
                rfl

/-- 同長Bool列の各位置一致flagをすべてANDすると、列全体の等値判定になる。 -/
theorem all_zipWith_decide_eq
    (left right : List Bool) (sameLength : left.length = right.length) :
    (List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
      left right).all id = decide (left = right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj sameLength
          by_cases headEqual : leftHead = rightHead
          · subst rightHead
            simp [inductionHypothesis rightTail tailLength]
          · simp [headEqual]

/-- 同じ長さのlittle-endian Bool列では、自然数値が等しければbit列自体も等しい。 -/
theorem littleEndianNat_injective_of_length_eq
    (left right : List Bool) (sameLength : left.length = right.length)
    (sameValue : littleEndianNat left = littleEndianNat right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj sameLength
          cases leftHead <;> cases rightHead
          · congr
            apply inductionHypothesis rightTail tailLength
            simp [littleEndianNat] at sameValue
            omega
          · simp [littleEndianNat] at sameValue
            omega
          · simp [littleEndianNat] at sameValue
            omega
          · congr
            apply inductionHypothesis rightTail tailLength
            simp [littleEndianNat] at sameValue
            omega

/-- 同長wordへ一bitを前置した比較は、上位tail比較とtail等値時の下位bit比較に分かれる。 -/
theorem littleEndianLessBits_cons
    (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (sameLength : leftTail.length = rightTail.length) :
    littleEndianLessBits (leftHead :: leftTail) (rightHead :: rightTail) =
      if (!leftHead) && rightHead && decide (leftTail = rightTail) then
        !(littleEndianLessBits leftTail rightTail)
      else
        littleEndianLessBits leftTail rightTail := by
  unfold littleEndianLessBits
  simp only [List.zipWith_cons_cons, littleEndianLessConditions, List.drop,
    boolParity]
  rw [all_zipWith_decide_eq leftTail rightTail sameLength]

/--
同長little-endian Bool列のbit位置条件parityは、それらが表す自然数のunsigned大小判定に
一致する。
-/
theorem littleEndianLessBits_eq_decide_lt
    (left right : List Bool) (sameLength : left.length = right.length) :
    littleEndianLessBits left right =
      decide (littleEndianNat left < littleEndianNat right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj sameLength
          have tailComparison := inductionHypothesis rightTail tailLength
          have tailValueNe_of_listNe (different : leftTail ≠ rightTail) :
              littleEndianNat leftTail ≠ littleEndianNat rightTail := by
            intro equal
            exact different <|
              littleEndianNat_injective_of_length_eq leftTail rightTail
                tailLength equal
          by_cases tailsEqual : leftTail = rightTail
          · subst rightTail
            cases leftHead <;> cases rightHead <;>
              simp [littleEndianLessBits_cons, tailComparison, littleEndianNat]
          · have valuesDifferent := tailValueNe_of_listNe tailsEqual
            by_cases tailLess :
                littleEndianNat leftTail < littleEndianNat rightTail
            · have fullLess (leftBit rightBit : Bool) :
                  littleEndianNat (leftBit :: leftTail) <
                    littleEndianNat (rightBit :: rightTail) := by
                cases leftBit <;> cases rightBit <;> simp [littleEndianNat] <;> omega
              cases leftHead <;> cases rightHead <;>
                rw [littleEndianLessBits_cons _ _ _ _ tailLength, tailComparison] <;>
                simp [tailsEqual, tailLess, fullLess]
            · have tailGreater :
                  littleEndianNat rightTail < littleEndianNat leftTail := by
                omega
              have fullNotLess (leftBit rightBit : Bool) :
                  ¬littleEndianNat (leftBit :: leftTail) <
                    littleEndianNat (rightBit :: rightTail) := by
                cases leftBit <;> cases rightBit <;> simp [littleEndianNat] <;> omega
              cases leftHead <;> cases rightHead <;>
                rw [littleEndianLessBits_cons _ _ _ _ tailLength, tailComparison] <;>
                simp [tailsEqual, tailLess, fullNotLess]

/-- little-endian Bool列の自然数値は、そのbit幅の2冪より小さい。 -/
theorem littleEndianNat_lt_pow (bits : List Bool) :
    littleEndianNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [littleEndianNat]
  | cons bit bits inductionHypothesis =>
      cases bit <;> simp [littleEndianNat, pow_succ] <;> omega

/-- `incrementBits`は固定bit幅で自然数値へ1を加える周期incrementである。 -/
theorem littleEndianNat_incrementBits (bits : List Bool) :
    littleEndianNat (incrementBits bits) =
      (littleEndianNat bits + 1) % (2 ^ bits.length) := by
  induction bits with
  | nil => simp [incrementBits, incrementBitsWithCarry, littleEndianNat]
  | cons bit bits inductionHypothesis =>
      cases bit with
      | false =>
          simp only [incrementBits, incrementBitsWithCarry,
            littleEndianNat, Bool.toNat_false, Nat.add_zero, List.length_cons]
          simp only [Bool.true_and, incrementBitsWithCarry_false, if_true,
            Bool.not_false, Bool.toNat_true]
          rw [Nat.mod_eq_of_lt]
          have bound := littleEndianNat_lt_pow bits
          rw [pow_succ]
          omega
      | true =>
          change 2 * littleEndianNat (incrementBits bits) =
            (2 * littleEndianNat bits + 1 + 1) % (2 ^ (bits.length + 1))
          rw [show 2 * littleEndianNat bits + 1 + 1 =
            2 * (littleEndianNat bits + 1) by omega]
          rw [pow_succ]
          rw [show 2 ^ bits.length * 2 = 2 * 2 ^ bits.length by omega]
          rw [Nat.mul_mod_mul_left]
          rw [inductionHypothesis]

/-- `decrementBits`は0で最大値へwrapし、それ以外では自然数値を1減らす。 -/
theorem littleEndianNat_decrementBits_conditional (bits : List Bool) :
    littleEndianNat (decrementBits bits) =
      if littleEndianNat bits = 0 then
        2 ^ bits.length - 1
      else
        littleEndianNat bits - 1 := by
  induction bits with
  | nil => simp [decrementBits, decrementBitsWithBorrow, littleEndianNat]
  | cons bit bits inductionHypothesis =>
      cases bit with
      | false =>
          change 2 * littleEndianNat (decrementBits bits) + 1 =
            if 2 * littleEndianNat bits = 0 then
              2 ^ (bits.length + 1) - 1
            else 2 * littleEndianNat bits - 1
          rw [inductionHypothesis, pow_succ]
          by_cases zero : littleEndianNat bits = 0
          · have powerPositive : 0 < 2 ^ bits.length := by positivity
            simp [zero]
            omega
          · have positive : 0 < littleEndianNat bits := Nat.pos_of_ne_zero zero
            simp [zero]
            omega
      | true =>
          simp only [decrementBits, decrementBitsWithBorrow, Bool.not_true,
            Bool.true_and, decrementBitsWithBorrow_false, littleEndianNat,
            Bool.toNat_true, List.length_cons]
          change 2 * littleEndianNat bits =
            if 2 * littleEndianNat bits + 1 = 0 then
              2 ^ (bits.length + 1) - 1
            else 2 * littleEndianNat bits + 1 - 1
          rw [if_neg (by omega)]
          omega

/-- `decrementBits`は固定bit幅で自然数値を1減らす周期decrementである。 -/
theorem littleEndianNat_decrementBits (bits : List Bool) :
    littleEndianNat (decrementBits bits) =
      (littleEndianNat bits + 2 ^ bits.length - 1) % (2 ^ bits.length) := by
  rw [littleEndianNat_decrementBits_conditional]
  have bound := littleEndianNat_lt_pow bits
  have modulusPositive : 0 < 2 ^ bits.length := by positivity
  by_cases zero : littleEndianNat bits = 0
  · simp only [zero, Nat.zero_add, if_pos]
    rw [Nat.mod_eq_of_lt]
    omega
  · rw [if_neg zero]
    have positive : 0 < littleEndianNat bits := Nat.pos_of_ne_zero zero
    rw [Nat.mod_eq_sub_mod (by omega)]
    have subtraction :
        littleEndianNat bits + 2 ^ bits.length - 1 - 2 ^ bits.length =
          littleEndianNat bits - 1 := by
      omega
    rw [subtraction]
    rw [Nat.mod_eq_of_lt]
    omega

/-- 周期increment回路はlittle-endian自然数へ1を加え、word幅の2冪でwrapする。 -/
theorem littleEndianNat_incrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    littleEndianNat
        (readWires word ((incrementWordMod2PowInPlaceCircuit word scratches).runBasis
          reversibleGatePermutation input)) =
      (littleEndianNat (readWires word input) + 1) % (2 ^ word.length) := by
  rw [readWires_incrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
    layoutNodup scratchZero]
  rw [littleEndianNat_incrementBits]
  simp [readWires]

/-- 周期decrement回路はlittle-endian自然数を1減らし、word幅の2冪でwrapする。 -/
theorem littleEndianNat_decrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    littleEndianNat
        (readWires word ((decrementWordMod2PowInPlaceCircuit word scratches).runBasis
          reversibleGatePermutation input)) =
      (littleEndianNat (readWires word input) + 2 ^ word.length - 1) %
        (2 ^ word.length) := by
  rw [readWires_decrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
    layoutNodup scratchZero]
  rw [littleEndianNat_decrementBits]
  simp [readWires]

/--
word等値回路は、clean flag/scratchを内部で計算・消去し、二つの同長wordが等しいとき
だけtargetを反転する。
-/
theorem runBasis_xorEqualityIntoTargetCircuit
    {ancillaQubits systemQubits : Nat}
    (left right flags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = flags.length)
    (rightLength : right.length = flags.length)
    (leftDisjointFlags : left.Disjoint flags)
    (rightDisjointFlags : right.Disjoint flags)
    (flagsDisjointScratch : flags.Disjoint scratches)
    (flagsNodup : flags.Nodup)
    (positiveLayout : (flags ++ scratches ++ [target]).Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (flagsZero : readWires flags input = List.replicate flags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (enoughScratch : flags.length ≤ scratches.length + 1) :
    (xorEqualityIntoTargetCircuit left right flags scratches target).runBasis
        reversibleGatePermutation input =
      if decide (readWires left input = readWires right input) then
        xBasisAction target input
      else input := by
  let compute := computeEqualityFlags left right flags
  let use := positiveMultiControlledX flags scratches target
  let computed := compute.runBasis reversibleGatePermutation input
  have flagValues :
      readWires flags computed =
        List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
          (readWires left input) (readWires right input) := by
    exact runBasis_computeEqualityFlags_readWires left right flags input
      leftLength rightLength leftDisjointFlags rightDisjointFlags flagsNodup flagsZero
  have scratchStillZero : ∀ wire ∈ scratches, computed wire = false := by
    have notInScratch : ∀ {wire : Wire ancillaQubits systemQubits},
        wire ∈ flags → wire ∉ scratches := by
      intro wire wireInFlags
      exact (List.disjoint_left.mp flagsDisjointScratch) wireInFlags
    intro wire member
    change (computeEqualityFlags left right flags).runBasis
      reversibleGatePermutation input wire = false
    rw [runBasis_computeEqualityFlags_outside left right flags wire input
      leftDisjointFlags rightDisjointFlags (by
        intro wireInFlags
        exact notInScratch wireInFlags member)]
    exact scratchZero wire member
  have conditionEqual :
      allWiresTrue flags computed =
        decide (readWires left input = readWires right input) := by
    unfold allWiresTrue
    rw [flagValues]
    apply all_zipWith_decide_eq
    simpa [readWires] using leftLength.trans rightLength.symm
  have targetAbsentFlags : target ∉ flags := by
    intro member
    have separated := (List.nodup_append.mp positiveLayout).2.2
    exact separated target (by simp [member]) target (by simp) rfl
  have useResult :
      use.runBasis reversibleGatePermutation computed =
        compute.runBasis reversibleGatePermutation
          (if decide (readWires left input = readWires right input) then
            xBasisAction target input
          else input) := by
    rw [show use.runBasis reversibleGatePermutation computed =
        if allWiresTrue flags computed then xBasisAction target computed else computed by
      exact runBasis_positiveMultiControlledX flags scratches target computed
        enoughScratch positiveLayout scratchStillZero]
    rw [conditionEqual]
    by_cases equalWords : readWires left input = readWires right input
    · simp only [decide_eq_true_eq, equalWords, if_true]
      exact (runBasis_computeEqualityFlags_x_commute left right flags target input
        leftDisjointFlags rightDisjointFlags targetAbsentLeft targetAbsentRight
        targetAbsentFlags).symm
    · simp [equalWords, compute, computed]
  change (Circuit.computeUseUncompute id compute use).runBasis
      reversibleGatePermutation input = _
  exact Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute use input _ useResult

/--
比較回路が等値flag計算後に実行する全bit分岐の反転parity。これは回路から独立した
有限Bool計算であり、次段で通常のunsigned大小関係へ同定する。
-/
def lessThanCondition
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) : Bool :=
  let computed := (computeEqualityFlags left right equalFlags).runBasis
    reversibleGatePermutation input
  boolControlProgramParity (lessThanControlProgram left right equalFlags) computed

/--
比較器のwire制御programを任意の基底状態で評価すると、読み出した三Bool列上の
bit位置条件parityに一致する。
-/
theorem boolControlProgramParity_lessThanControlProgram
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    boolControlProgramParity (lessThanControlProgram left right equalFlags) input =
      boolParity (littleEndianLessConditions
        (readWires left input) (readWires right input)
        (readWires equalFlags input)) := by
  rw [boolControlProgramParity_eq_boolParity]
  congr 1
  induction left generalizing right equalFlags with
  | nil => simp [lessThanControlProgram, littleEndianLessConditions, readWires]
  | cons leftBit left inductionHypothesis =>
      cases right with
      | nil => simp [lessThanControlProgram, littleEndianLessConditions, readWires]
      | cons rightBit right =>
          have higherValues :
              ((equalFlags.drop 1).map fun wire => (wire, true)).all
                  (fun control => decide (input control.1 = control.2)) =
                ((equalFlags.drop 1).map input).all id := by
            rw [List.all_map, List.all_map]
            apply List.all_congr rfl
            intro wire
            change decide (input wire = true) = input wire
            cases input wire <;> rfl
          simp only [lessThanControlProgram, List.map_cons,
            littleEndianLessConditions, readWires]
          congr 1
          · simp only [boolControlsSatisfied, List.all_cons]
            rw [higherValues]
            cases input leftBit <;> cases input rightBit <;> simp
          · simpa [readWires, List.map_drop] using
              inductionHypothesis right (equalFlags.drop 1)

/--
等値flagがcleanな状態から計算された場合、比較回路の分岐parityは純粋な
`littleEndianLessBits`判定に一致する。
-/
theorem lessThanCondition_eq_littleEndianLessBits
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsNodup : equalFlags.Nodup)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false) :
    lessThanCondition left right equalFlags input =
      littleEndianLessBits (readWires left input) (readWires right input) := by
  let computed := (computeEqualityFlags left right equalFlags).runBasis
    reversibleGatePermutation input
  have leftUnchanged : readWires left computed = readWires left input := by
    apply List.map_congr_left
    intro wire member
    exact runBasis_computeEqualityFlags_outside left right equalFlags wire input
      leftDisjointFlags rightDisjointFlags
      ((List.disjoint_left.mp leftDisjointFlags) member)
  have rightUnchanged : readWires right computed = readWires right input := by
    apply List.map_congr_left
    intro wire member
    exact runBasis_computeEqualityFlags_outside left right equalFlags wire input
      leftDisjointFlags rightDisjointFlags
      ((List.disjoint_left.mp rightDisjointFlags) member)
  have flagValues :
      readWires equalFlags computed =
        List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
          (readWires left input) (readWires right input) := by
    exact runBasis_computeEqualityFlags_readWires left right equalFlags input
      leftLength rightLength leftDisjointFlags rightDisjointFlags flagsNodup flagsZero
  unfold lessThanCondition
  rw [boolControlProgramParity_lessThanControlProgram]
  rw [leftUnchanged, rightUnchanged, flagValues]
  rfl

/--
一般幅の`xorLessThanIntoTargetCircuit`回路は、各bit分岐のparityが1のときだけtargetを反転し、等値flagと
scratchを入力値0へ戻す。
-/
theorem runBasis_xorLessThanIntoTargetCircuit
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsDisjointScratch : equalFlags.Disjoint scratches)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (targetAbsentFlags : target ∉ equalFlags)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (programEnough : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      controls.length ≤ scratches.length + 1)
    (programLayout : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup) :
    (xorLessThanIntoTargetCircuit left right equalFlags scratches target).runBasis
        reversibleGatePermutation input =
      if lessThanCondition left right equalFlags input then
        xBasisAction target input
      else input := by
  let compute := computeEqualityFlags left right equalFlags
  let program := lessThanControlProgram left right equalFlags
  let use := boolControlProgram program scratches target
  let computed := compute.runBasis reversibleGatePermutation input
  have computedScratchZero : ∀ wire ∈ scratches, computed wire = false := by
    have notInScratch : ∀ {wire : Wire ancillaQubits systemQubits},
        wire ∈ equalFlags → wire ∉ scratches := by
      intro wire wireInFlags
      exact (List.disjoint_left.mp flagsDisjointScratch) wireInFlags
    intro wire member
    change (computeEqualityFlags left right equalFlags).runBasis
      reversibleGatePermutation input wire = false
    rw [runBasis_computeEqualityFlags_outside left right equalFlags wire input
      leftDisjointFlags rightDisjointFlags (by
        intro wireInFlags
        exact notInScratch wireInFlags member)]
    exact scratchZero wire member
  have useResult :
      use.runBasis reversibleGatePermutation computed =
        compute.runBasis reversibleGatePermutation
          (if lessThanCondition left right equalFlags input then
            xBasisAction target input
          else input) := by
    rw [show use.runBasis reversibleGatePermutation computed =
        if boolControlProgramParity program computed then
          xBasisAction target computed
        else computed by
      exact runBasis_boolControlProgram program scratches target computed
        programEnough programLayout computedScratchZero]
    change (if lessThanCondition left right equalFlags input then
        xBasisAction target computed
      else computed) = _
    by_cases enabled : lessThanCondition left right equalFlags input
    · simp only [enabled, if_true]
      exact (runBasis_computeEqualityFlags_x_commute left right equalFlags target input
        leftDisjointFlags rightDisjointFlags targetAbsentLeft targetAbsentRight
        targetAbsentFlags).symm
    · simp [enabled, compute, computed]
  change (Circuit.computeUseUncompute id compute use).runBasis
      reversibleGatePermutation input = _
  exact Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute use input _ useResult

/--
clean layout上の`xorLessThanIntoTargetCircuit`回路は、読み出したlittle-endian二wordの純粋な大小判定に
従ってtargetだけを反転する。
-/
theorem runBasis_xorLessThanIntoTargetCircuit_bits
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsDisjointScratch : equalFlags.Disjoint scratches)
    (flagsNodup : equalFlags.Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (targetAbsentFlags : target ∉ equalFlags)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (programEnough : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      controls.length ≤ scratches.length + 1)
    (programLayout : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup) :
    (xorLessThanIntoTargetCircuit left right equalFlags scratches target).runBasis
        reversibleGatePermutation input =
      if littleEndianLessBits (readWires left input) (readWires right input) then
        xBasisAction target input
      else input := by
  rw [runBasis_xorLessThanIntoTargetCircuit left right equalFlags scratches target input
    leftDisjointFlags rightDisjointFlags flagsDisjointScratch targetAbsentLeft
    targetAbsentRight targetAbsentFlags scratchZero programEnough programLayout]
  rw [lessThanCondition_eq_littleEndianLessBits left right equalFlags input
    leftLength rightLength leftDisjointFlags rightDisjointFlags flagsNodup flagsZero]

/-- clean layout上の`xorLessThanIntoTargetCircuit`回路は、little-endian自然数の通常の`<`を実装する。 -/
theorem runBasis_xorLessThanIntoTargetCircuit_nat
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsDisjointScratch : equalFlags.Disjoint scratches)
    (flagsNodup : equalFlags.Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (targetAbsentFlags : target ∉ equalFlags)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (programEnough : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      controls.length ≤ scratches.length + 1)
    (programLayout : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup) :
    (xorLessThanIntoTargetCircuit left right equalFlags scratches target).runBasis
        reversibleGatePermutation input =
      if decide (littleEndianNat (readWires left input) <
          littleEndianNat (readWires right input)) then
        xBasisAction target input
      else input := by
  rw [runBasis_xorLessThanIntoTargetCircuit_bits left right equalFlags scratches target input
    leftLength rightLength leftDisjointFlags rightDisjointFlags flagsDisjointScratch
    flagsNodup targetAbsentLeft targetAbsentRight targetAbsentFlags flagsZero scratchZero
    programEnough programLayout]
  rw [littleEndianLessBits_eq_decide_lt]
  simpa [readWires] using leftLength.trans rightLength.symm

/-- 比較programの一分岐が使う制御本数は等値flag本数より高々一つ多い。 -/
theorem lessThanControlProgram_controls_length_le
    {ancillaQubits systemQubits : Nat} :
    ∀ (left right equalFlags : List (Wire ancillaQubits systemQubits))
      (controls : List (Wire ancillaQubits systemQubits × Bool)),
      left.length = equalFlags.length →
      controls ∈ lessThanControlProgram left right equalFlags →
      controls.length ≤ equalFlags.length + 1
  | [], _, _, _, _, member => by simp [lessThanControlProgram] at member
  | _ :: _, [], _, _, _, member => by simp [lessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls,
      lengthEqual, member => by
      simp only [lessThanControlProgram, List.mem_cons] at member
      rcases member with rfl | tailMember
      · cases equalFlags with
        | nil => simp at lengthEqual
        | cons _ equalFlags => simp
      · have tailLength : left.length = (equalFlags.drop 1).length := by
          simp only [List.length_cons, List.length_drop] at lengthEqual ⊢
          omega
        have bound := lessThanControlProgram_controls_length_le left right
          (equalFlags.drop 1) controls tailLength tailMember
        simp only [List.length_drop] at bound
        omega

/-- 元の三領域に重複がなければ、比較programの各制御wire列にも重複がない。 -/
theorem lessThanControlProgram_controls_nodup
    {ancillaQubits systemQubits : Nat} :
    ∀ (left right equalFlags : List (Wire ancillaQubits systemQubits))
      (controls : List (Wire ancillaQubits systemQubits × Bool)),
      (left ++ right ++ equalFlags).Nodup →
      controls ∈ lessThanControlProgram left right equalFlags →
      (controls.map Prod.fst).Nodup
  | [], _, _, _, _, member => by simp [lessThanControlProgram] at member
  | _ :: _, [], _, _, _, member => by simp [lessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls,
      sourceNodup, member => by
      simp only [lessThanControlProgram, List.mem_cons] at member
      have leftSplit :
          (leftBit :: left).Nodup ∧
          ((rightBit :: right) ++ equalFlags).Nodup ∧
          ∀ a ∈ leftBit :: left, ∀ b ∈ (rightBit :: right) ++ equalFlags,
            a ≠ b := by
        rw [← List.nodup_append]
        simpa [List.append_assoc] using sourceNodup
      have rightSplit := List.nodup_append.mp leftSplit.2.1
      rcases member with rfl | tailMember
      · simp only [List.map_cons, List.map_map]
        have mapIdentity :
            List.map
                (Prod.fst ∘ fun wire : Wire ancillaQubits systemQubits =>
                  (wire, true))
                (equalFlags.drop 1) =
              equalFlags.drop 1 := by
          induction equalFlags.drop 1 with
          | nil => rfl
          | cons wire wires inductionHypothesis =>
              simp only [List.map_cons, Function.comp_apply, inductionHypothesis]
        rw [mapIdentity]
        change (leftBit :: rightBit :: equalFlags.drop 1).Nodup
        rw [List.nodup_cons, List.nodup_cons]
        refine ⟨?_, ?_, rightSplit.2.1.sublist (List.drop_sublist 1 equalFlags)⟩
        · intro member
          rcases List.mem_cons.mp member with equal | flagMember
          · exact leftSplit.2.2 leftBit (by simp) rightBit (by simp) equal
          · exact leftSplit.2.2 leftBit (by simp) _
              (List.mem_append_right _ (List.mem_of_mem_drop flagMember)) rfl
        · intro flagMember
          exact rightSplit.2.2 rightBit (by simp) _
            (List.mem_of_mem_drop flagMember) rfl
      · have tailLeftNodup : left.Nodup := leftSplit.1.tail
        have tailRightNodup : right.Nodup := rightSplit.1.tail
        have tailFlagsNodup : (equalFlags.drop 1).Nodup :=
          rightSplit.2.1.sublist (List.drop_sublist 1 equalFlags)
        have tailLeftRightDisjoint : ∀ a ∈ left, ∀ b ∈ right, a ≠ b := by
          intro a aMember b bMember
          exact leftSplit.2.2 a (by simp [aMember]) b
            (List.mem_append_left _ (by simp [bMember]))
        have tailLeftFlagsDisjoint : ∀ a ∈ left,
            ∀ b ∈ equalFlags.drop 1, a ≠ b := by
          intro a aMember b bMember
          exact leftSplit.2.2 a (by simp [aMember]) b
            (List.mem_append_right _ (List.mem_of_mem_drop bMember))
        have tailRightFlagsDisjoint : ∀ a ∈ right,
            ∀ b ∈ equalFlags.drop 1, a ≠ b := by
          intro a aMember b bMember
          exact rightSplit.2.2 a (by simp [aMember]) b
            (List.mem_of_mem_drop bMember)
        have tailSourceNodup :
            (left ++ right ++ equalFlags.drop 1).Nodup := by
          rw [List.nodup_append]
          refine ⟨?_, tailFlagsNodup, ?_⟩
          · rw [List.nodup_append]
            exact ⟨tailLeftNodup, tailRightNodup, tailLeftRightDisjoint⟩
          · intro a aMember b bMember
            rcases List.mem_append.mp aMember with aLeft | aRight
            · exact tailLeftFlagsDisjoint a aLeft b bMember
            · exact tailRightFlagsDisjoint a aRight b bMember
        exact lessThanControlProgram_controls_nodup left right
          (equalFlags.drop 1) controls tailSourceNodup tailMember

/-- 比較programの制御wireは左右wordまたは等値flagのいずれかに属する。 -/
theorem lessThanControlProgram_source_mem
    {ancillaQubits systemQubits : Nat} :
    ∀ (left right equalFlags : List (Wire ancillaQubits systemQubits))
      (controls : List (Wire ancillaQubits systemQubits × Bool)),
      controls ∈ lessThanControlProgram left right equalFlags →
      ∀ control ∈ controls, control.1 ∈ left ++ right ++ equalFlags
  | [], _, _, _, member => by simp [lessThanControlProgram] at member
  | _ :: _, [], _, _, member => by simp [lessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls, member => by
      simp only [lessThanControlProgram, List.mem_cons] at member
      rcases member with rfl | tailMember
      · intro control controlMember
        simp only [List.mem_cons] at controlMember
        rcases controlMember with rfl | controlMember
        · simp
        · rcases controlMember with rfl | higherMember
          · simp
          · rcases List.mem_map.mp higherMember with ⟨wire, wireMember, rfl⟩
            have originalMember : wire ∈ equalFlags :=
              List.mem_of_mem_drop wireMember
            simp [originalMember]
      · intro control controlMember
        have tailResult := lessThanControlProgram_source_mem left right
          (equalFlags.drop 1) controls tailMember control controlMember
        rcases List.mem_append.mp tailResult with leftRightMember | flagMember
        · rcases List.mem_append.mp leftRightMember with leftMember | rightMember
          · simp [leftMember]
          · simp [rightMember]
        · have originalMember : control.1 ∈ equalFlags :=
            List.mem_of_mem_drop flagMember
          simp [originalMember]

/-- 全比較領域が重複しなければ、任意分岐の制御・scratch・targetにも重複がない。 -/
theorem lessThanControlProgram_layout
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (fullLayout :
      (left ++ right ++ equalFlags ++ scratches ++ [target]).Nodup) :
    ∀ controls ∈ lessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup := by
  intro controls controlsMember
  let sources := left ++ right ++ equalFlags
  let rest := scratches ++ [target]
  have split : sources.Nodup ∧ rest.Nodup ∧
      ∀ a ∈ sources, ∀ b ∈ rest, a ≠ b := by
    rw [← List.nodup_append]
    simpa [sources, rest, List.append_assoc] using fullLayout
  have combined : (controls.map Prod.fst ++ rest).Nodup := by
    rw [List.nodup_append]
    refine ⟨lessThanControlProgram_controls_nodup left right equalFlags controls
      split.1 controlsMember, split.2.1, ?_⟩
    intro wire wireMember other otherMember
    have sourceMember : wire ∈ sources := by
      rcases List.mem_map.mp wireMember with ⟨control, controlMember, rfl⟩
      exact lessThanControlProgram_source_mem left right equalFlags controls
        controlsMember control controlMember
    exact split.2.2 wire sourceMember other otherMember
  simpa [rest, List.append_assoc] using combined

/--
全領域の一括`Nodup`とscratch本数だけから、一般比較器の通常の自然数大小仕様を使える。
個別回路で制御分岐ごとのlayout義務を繰り返す必要をなくす補題である。
-/
theorem runBasis_xorLessThanIntoTargetCircuit_nat_of_layout
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (fullLayout :
      (left ++ right ++ equalFlags ++ scratches ++ [target]).Nodup)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (scratchEnough : equalFlags.length ≤ scratches.length) :
    (xorLessThanIntoTargetCircuit left right equalFlags scratches target).runBasis
        reversibleGatePermutation input =
      if decide (littleEndianNat (readWires left input) <
          littleEndianNat (readWires right input)) then
        xBasisAction target input
      else input := by
  have leftSplit : left.Nodup ∧
      (right ++ equalFlags ++ scratches ++ [target]).Nodup ∧
      ∀ a ∈ left, ∀ b ∈ right ++ equalFlags ++ scratches ++ [target], a ≠ b := by
    rw [← List.nodup_append]
    simpa [List.append_assoc] using fullLayout
  have rightSplit : right.Nodup ∧
      (equalFlags ++ scratches ++ [target]).Nodup ∧
      ∀ a ∈ right, ∀ b ∈ equalFlags ++ scratches ++ [target], a ≠ b := by
    rw [← List.nodup_append]
    simpa [List.append_assoc] using leftSplit.2.1
  have flagSplit : equalFlags.Nodup ∧
      (scratches ++ [target]).Nodup ∧
      ∀ a ∈ equalFlags, ∀ b ∈ scratches ++ [target], a ≠ b := by
    rw [← List.nodup_append]
    simpa [List.append_assoc] using rightSplit.2.1
  have leftDisjointFlags : left.Disjoint equalFlags := by
    rw [List.disjoint_left]
    intro a aMember aFlagMember
    exact leftSplit.2.2 a aMember a (by
      simpa [List.append_assoc] using
        (List.mem_append_right right
          (List.mem_append_left (scratches ++ [target]) aFlagMember))) rfl
  have rightDisjointFlags : right.Disjoint equalFlags := by
    rw [List.disjoint_left]
    intro a aMember aFlagMember
    exact rightSplit.2.2 a aMember a (by
      simpa [List.append_assoc] using
        (List.mem_append_left (scratches ++ [target]) aFlagMember)) rfl
  have flagsDisjointScratch : equalFlags.Disjoint scratches := by
    rw [List.disjoint_left]
    intro a aMember aScratchMember
    exact flagSplit.2.2 a aMember a
      (List.mem_append_left [target] aScratchMember) rfl
  have targetAbsentLeft : target ∉ left := by
    intro member
    exact leftSplit.2.2 target member target (by simp) rfl
  have targetAbsentRight : target ∉ right := by
    intro member
    exact rightSplit.2.2 target member target (by simp) rfl
  have targetAbsentFlags : target ∉ equalFlags := by
    intro member
    exact flagSplit.2.2 target member target
      (List.mem_append_right scratches (List.mem_singleton_self target)) rfl
  apply runBasis_xorLessThanIntoTargetCircuit_nat left right equalFlags scratches target input
    leftLength rightLength leftDisjointFlags rightDisjointFlags
    flagsDisjointScratch flagSplit.1 targetAbsentLeft targetAbsentRight
    targetAbsentFlags flagsZero scratchZero
  · intro controls controlsMember
    have bound := lessThanControlProgram_controls_length_le left right equalFlags
      controls leftLength controlsMember
    omega
  · exact lessThanControlProgram_layout left right equalFlags scratches target fullLayout

/-- reversible OR回路は初期0のtargetへ`left OR right`を計算する。 -/
theorem runBasis_reversibleOrXor_target
    {ancillaQubits systemQubits : Nat}
    (left right target : Wire ancillaQubits systemQubits)
    (leftDifferent : left ≠ target)
    (rightDifferent : right ≠ target)
    (controlsDifferent : left ≠ right)
    (input : JointBasis ancillaQubits systemQubits)
    (targetZero : input target = false) :
    (reversibleOrXor left right target).runBasis reversibleGatePermutation input target =
      (input left || input right) := by
  simp only [reversibleOrXor, runBasis_seq,
    runBasis_safeCnot left target leftDifferent,
    runBasis_safeCnot right target rightDifferent,
    runBasis_safeToffoli left right target controlsDifferent leftDifferent rightDifferent]
  cases leftValue : input left <;> cases rightValue : input right <;>
    simp [cnotBasisAction, toffoliBasisAction, targetZero,
      leftDifferent, rightDifferent, leftValue, rightValue]

/-- reversible OR回路はtarget以外の全wireを変更しない。 -/
theorem runBasis_reversibleOrXor_other
    {ancillaQubits systemQubits : Nat}
    (left right target wire : Wire ancillaQubits systemQubits)
    (leftDifferent : left ≠ target)
    (rightDifferent : right ≠ target)
    (controlsDifferent : left ≠ right)
    (wireDifferent : wire ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    (reversibleOrXor left right target).runBasis reversibleGatePermutation input wire =
      input wire := by
  simp only [reversibleOrXor, runBasis_seq,
    runBasis_safeCnot left target leftDifferent,
    runBasis_safeCnot right target rightDifferent,
    runBasis_safeToffoli left right target controlsDifferent leftDifferent rightDifferent]
  simp [cnotBasisAction, toffoliBasisAction, wireDifferent]

/-- Bool列の各位置に、その位置から右端までのORを並べる。 -/
def suffixOrBits : List Bool → List Bool
  | [] => []
  | bit :: bits =>
      let tail := suffixOrBits bits
      (bit || tail.headD false) :: tail

/-- suffix OR列は入力Bool列と同じ長さを持つ。 -/
@[simp] theorem suffixOrBits_length (bits : List Bool) :
    (suffixOrBits bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp [suffixOrBits, inductionHypothesis]

/-- suffix OR列の先頭は入力列全体の論理和である。 -/
theorem suffixOrBits_headD (bits : List Bool) :
    (suffixOrBits bits).headD false = bits.any id := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp only [suffixOrBits, List.headD_cons, List.any_cons]
      rw [inductionHypothesis]
      cases bit <;> cases bits.any id <;> rfl

/-- suffix OR列の任意位置は、入力列を同じ位置までdropした残り全体の論理和である。 -/
theorem suffixOrBits_getD (bits : List Bool) (index : Nat) :
    (suffixOrBits bits)[index]?.getD false = (bits.drop index).any id := by
  induction bits generalizing index with
  | nil => simp [suffixOrBits]
  | cons bit bits inductionHypothesis =>
      cases index with
      | zero =>
          simpa [suffixOrBits] using suffixOrBits_headD (bit :: bits)
      | succ index =>
          simpa [suffixOrBits] using inductionHypothesis index

/--
同長で互いに素なinput/suffix配置では、suffix OR回路はsuffix列外のwireを変更しない。
-/
theorem runBasis_suffixOrCircuit_outside
    {ancillaQubits systemQubits : Nat}
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (sameLength : inputWires.length = suffixWires.length)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (suffixNodup : suffixWires.Nodup)
    (outside : wire ∉ suffixWires) :
    (suffixOrCircuit inputWires suffixWires).runBasis
        reversibleGatePermutation input wire = input wire := by
  induction inputWires generalizing suffixWires input with
  | nil =>
      cases suffixWires with
      | nil => rfl
      | cons suffixHead suffixTail => simp at sameLength
  | cons inputHead inputTail inductionHypothesis =>
      cases suffixWires with
      | nil => simp at sameLength
      | cons suffixHead suffixTail =>
          have tailLength : inputTail.length = suffixTail.length := by
            simpa using Nat.succ.inj sameLength
          have inputHeadDifferentSuffixHead : inputHead ≠ suffixHead := by
            intro equal
            have notInSuffix : inputHead ∉ suffixHead :: suffixTail :=
              (List.disjoint_left.mp inputDisjointSuffix) (by simp)
            exact notInSuffix (by simp [equal])
          have wireDifferentSuffixHead : wire ≠ suffixHead := by
            intro equal
            apply outside
            simp [equal]
          cases inputTail with
          | nil =>
              cases suffixTail with
              | nil =>
                  rw [suffixOrCircuit,
                    runBasis_safeCnot inputHead suffixHead inputHeadDifferentSuffixHead]
                  exact cnotBasisAction_other inputHead suffixHead wire
                    wireDifferentSuffixHead input
              | cons suffixNext suffixTail => simp at tailLength
          | cons inputNext inputTail =>
              cases suffixTail with
              | nil => simp at tailLength
              | cons suffixNext suffixTail =>
                  have tailDisjoint :
                      (inputNext :: inputTail).Disjoint
                        (suffixNext :: suffixTail) := by
                    rw [List.disjoint_left]
                    intro element memberInput memberSuffix
                    have notInSuffix : element ∉ suffixHead :: suffixNext :: suffixTail :=
                      (List.disjoint_left.mp inputDisjointSuffix)
                        (by simp [memberInput])
                    exact notInSuffix (by simp [memberSuffix])
                  have tailSuffixNodup : (suffixNext :: suffixTail).Nodup :=
                    (List.nodup_cons.mp suffixNodup).2
                  have inputHeadDifferentSuffixNext : inputHead ≠ suffixNext := by
                    intro equal
                    have notInSuffix : inputHead ∉ suffixHead :: suffixNext :: suffixTail :=
                      (List.disjoint_left.mp inputDisjointSuffix) (by simp)
                    exact notInSuffix (by simp [equal])
                  have suffixNextDifferentHead : suffixNext ≠ suffixHead := by
                    intro equal
                    exact (List.nodup_cons.mp suffixNodup).1 (by simp [equal])
                  have wireOutsideTail : wire ∉ suffixNext :: suffixTail := by
                    intro member
                    apply outside
                    simp [member]
                  rw [suffixOrCircuit, runBasis_seq]
                  rw [runBasis_reversibleOrXor_other inputHead suffixNext suffixHead wire
                    inputHeadDifferentSuffixHead suffixNextDifferentHead
                    inputHeadDifferentSuffixNext wireDifferentSuffixHead]
                  exact inductionHypothesis (suffixNext :: suffixTail) input tailLength
                    tailDisjoint tailSuffixNodup wireOutsideTail

/--
同長で互いに素なinput/suffix配置と0初期化suffixに対して、suffix OR回路は
各位置から右端までのORをsuffix列へ正確に計算する。
-/
theorem readWires_suffixOrCircuit
    {ancillaQubits systemQubits : Nat}
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sameLength : inputWires.length = suffixWires.length)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (suffixNodup : suffixWires.Nodup)
    (suffixZero : readWires suffixWires input =
      List.replicate suffixWires.length false) :
    readWires suffixWires
        ((suffixOrCircuit inputWires suffixWires).runBasis
          reversibleGatePermutation input) =
      suffixOrBits (readWires inputWires input) := by
  induction inputWires generalizing suffixWires input with
  | nil =>
      cases suffixWires with
      | nil => rfl
      | cons suffixHead suffixTail => simp at sameLength
  | cons inputHead inputTail inductionHypothesis =>
      cases suffixWires with
      | nil => simp at sameLength
      | cons suffixHead suffixTail =>
          have tailLength : inputTail.length = suffixTail.length := by
            simpa using Nat.succ.inj sameLength
          have inputHeadDifferentSuffixHead : inputHead ≠ suffixHead := by
            intro equal
            have notInSuffix : inputHead ∉ suffixHead :: suffixTail :=
              (List.disjoint_left.mp inputDisjointSuffix) (by simp)
            exact notInSuffix (by simp [equal])
          have suffixHeadZero : input suffixHead = false := by
            have firstValue := congrArg List.head? suffixZero
            simpa [readWires, List.replicate_succ, ← Nat.succ_eq_add_one]
              using firstValue
          cases inputTail with
          | nil =>
              cases suffixTail with
              | nil =>
                  rw [suffixOrCircuit,
                    runBasis_safeCnot inputHead suffixHead inputHeadDifferentSuffixHead]
                  simp [readWires, suffixOrBits, cnotBasisAction, suffixHeadZero]
              | cons suffixNext suffixTail => simp at tailLength
          | cons inputNext inputTail =>
              cases suffixTail with
              | nil => simp at tailLength
              | cons suffixNext suffixTail =>
                  let tailInputs := inputNext :: inputTail
                  let tailSuffix := suffixNext :: suffixTail
                  let tailState :=
                    (suffixOrCircuit tailInputs tailSuffix).runBasis
                      reversibleGatePermutation input
                  have tailDisjoint : tailInputs.Disjoint tailSuffix := by
                    rw [List.disjoint_left]
                    intro element memberInput memberSuffix
                    change element ∈ inputNext :: inputTail at memberInput
                    change element ∈ suffixNext :: suffixTail at memberSuffix
                    have notInSuffix : element ∉ suffixHead :: suffixNext :: suffixTail :=
                      (List.disjoint_left.mp inputDisjointSuffix)
                        (List.mem_cons_of_mem inputHead memberInput)
                    exact notInSuffix (List.mem_cons_of_mem suffixHead memberSuffix)
                  have tailSuffixNodup : tailSuffix.Nodup := by
                    exact (List.nodup_cons.mp suffixNodup).2
                  have tailZero : readWires tailSuffix input =
                      List.replicate tailSuffix.length false := by
                    have tailValues := congrArg List.tail suffixZero
                    simpa [readWires, tailSuffix] using tailValues
                  have tailResult : readWires tailSuffix tailState =
                      suffixOrBits (readWires tailInputs input) := by
                    exact inductionHypothesis tailSuffix input tailLength tailDisjoint
                      tailSuffixNodup tailZero
                  have inputHeadOutsideTail : inputHead ∉ tailSuffix := by
                    intro member
                    change inputHead ∈ suffixNext :: suffixTail at member
                    have notInSuffix : inputHead ∉ suffixHead :: suffixNext :: suffixTail :=
                      (List.disjoint_left.mp inputDisjointSuffix) (by simp)
                    exact notInSuffix (List.mem_cons_of_mem suffixHead member)
                  have suffixHeadOutsideTail : suffixHead ∉ tailSuffix := by
                    exact (List.nodup_cons.mp suffixNodup).1
                  have inputHeadValue : tailState inputHead = input inputHead := by
                    exact runBasis_suffixOrCircuit_outside tailInputs tailSuffix inputHead
                      input tailLength tailDisjoint tailSuffixNodup inputHeadOutsideTail
                  have suffixHeadValue : tailState suffixHead = false := by
                    change
                      (suffixOrCircuit tailInputs tailSuffix).runBasis
                          reversibleGatePermutation input suffixHead = false
                    rw [runBasis_suffixOrCircuit_outside tailInputs tailSuffix suffixHead
                      input tailLength tailDisjoint tailSuffixNodup suffixHeadOutsideTail]
                    exact suffixHeadZero
                  have suffixNextValue : tailState suffixNext =
                      (suffixOrBits (readWires tailInputs input)).headD false := by
                    have firstValue := congrArg (fun bits => bits.headD false) tailResult
                    simpa [readWires, tailSuffix] using firstValue
                  have inputHeadDifferentSuffixNext : inputHead ≠ suffixNext := by
                    intro equal
                    apply inputHeadOutsideTail
                    simp [tailSuffix, equal]
                  have suffixNextDifferentHead : suffixNext ≠ suffixHead := by
                    intro equal
                    exact suffixHeadOutsideTail (by simp [tailSuffix, equal])
                  have tailPreserved :
                      readWires tailSuffix
                          ((reversibleOrXor inputHead suffixNext suffixHead).runBasis
                            reversibleGatePermutation tailState) =
                        readWires tailSuffix tailState := by
                    apply List.map_congr_left
                    intro wire member
                    apply runBasis_reversibleOrXor_other inputHead suffixNext suffixHead wire
                      inputHeadDifferentSuffixHead suffixNextDifferentHead
                      inputHeadDifferentSuffixNext
                    intro equal
                    apply suffixHeadOutsideTail
                    simpa [equal] using member
                  rw [suffixOrCircuit, runBasis_seq]
                  change
                    ((reversibleOrXor inputHead suffixNext suffixHead).runBasis
                        reversibleGatePermutation tailState) suffixHead ::
                      readWires tailSuffix
                        ((reversibleOrXor inputHead suffixNext suffixHead).runBasis
                          reversibleGatePermutation tailState) =
                    (input inputHead ||
                        (suffixOrBits (readWires tailInputs input)).headD false) ::
                      suffixOrBits (readWires tailInputs input)
                  rw [runBasis_reversibleOrXor_target inputHead suffixNext suffixHead
                    inputHeadDifferentSuffixHead suffixNextDifferentHead
                    inputHeadDifferentSuffixNext tailState suffixHeadValue]
                  rw [inputHeadValue, suffixNextValue, tailPreserved, tailResult]

end ReversibleCircuit

end ProbabilityGeneratorQProof
