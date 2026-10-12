import QLean.Circuits.Foundation.MultiControlledRotation
import QLean.Circuits.Foundation.QuantumFourier

/-!
# 多重制御Ryの疎な正しさ

cleanなAND scratchを使う基本ゲート分解について、全体行列を展開せず、Toffoli置換による
共役と一量子ビット`Ry`の二項作用だけで一般幅の行列要素を証明する。
-/

open Matrix

namespace VerifiedCircuitCore

noncomputable section

namespace ReversibleCircuit

/-- 指定wire列の計算基底bitを同じ順序で読む。 -/
def readWires {qubits : Nat} (wires : List (Fin qubits))
    (input : QubitBasis qubits) : List Bool :=
  wires.map input

/-- 指定wire列がすべて真であるかを判定する。 -/
def allWiresTrue {qubits : Nat} (wires : List (Fin qubits))
    (input : QubitBasis qubits) : Bool :=
  (readWires wires input).all id

/-- 一要素をリストの先頭から途中へ移す置換。 -/
theorem perm_cons_append {α : Type*} (value : α) (middle suffix : List α) :
    (value :: middle ++ suffix).Perm (middle ++ value :: suffix) :=
  List.perm_middle.symm

/-- Toffoli標的以外のwire値は保存される。 -/
theorem toffoliBasisAction_other {qubits : Nat}
    (control₁ control₂ target wire : Fin qubits) (different : wire ≠ target)
    (input : QubitBasis qubits) :
    toffoliBasisAction control₁ control₂ target input wire = input wire := by
  simp [toffoliBasisAction, xorWire, different]

/-- Toffoli標的を含まないwire列の読出しは保存される。 -/
theorem readWires_toffoliBasisAction_of_not_mem {qubits : Nat}
    (wires : List (Fin qubits)) (control₁ control₂ target : Fin qubits)
    (input : QubitBasis qubits) (targetAbsent : target ∉ wires) :
    readWires wires (toffoliBasisAction control₁ control₂ target input) =
      readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact toffoliBasisAction_other control₁ control₂ target wire
    (fun equal => targetAbsent (equal ▸ member)) input

end ReversibleCircuit

/-- 固定二量子ビット上の二CNOT・二半角回転はcontrolled-Ryに等しい。 -/
theorem local_controlledRy_decomposition (angle : ℝ) :
    localCnotOperator * localOnTarget (localRy (-angle / 2)) *
        localCnotOperator * localOnTarget (localRy (angle / 2)) =
      localControlledOperator (localRy angle) := by
  let quarter : ℂ := (angle : ℂ) / 2 / 2
  have negQuarter : -(angle : ℂ) / 2 / 2 = -quarter := by
    dsimp [quarter]
    ring
  have positiveQuarter : (angle : ℂ) / 2 / 2 = quarter := rfl
  have halfAngle : (angle : ℂ) / 2 = 2 * quarter := by
    simp [quarter]
    ring
  have cosHalf : Complex.cos ((angle : ℂ) / 2) =
      Complex.cos quarter ^ 2 - Complex.sin quarter ^ 2 := by
    rw [halfAngle, Complex.cos_two_mul']
  have sinHalf : Complex.sin ((angle : ℂ) / 2) =
      2 * Complex.sin quarter * Complex.cos quarter := by
    rw [halfAngle, Complex.sin_two_mul]
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fintype.sum_prod_type] <;>
    simp [localCnotOperator, localOnTarget,
      localControlledOperator, localRy]
  all_goals
    rw [negQuarter, positiveQuarter]
    simp only [Complex.cos_neg, Complex.sin_neg]
    try rw [cosHalf]
    try rw [sinHalf]
    ring_nf
  all_goals
    first
    | exact Complex.sin_sq_add_cos_sq quarter
    | exact
        (add_comm (Complex.cos quarter ^ 2) (Complex.sin quarter ^ 2)).trans
          (Complex.sin_sq_add_cos_sq quarter)

/-- 一制御Ryの四基本gate分解は任意wire上の理想controlled-Ryに一致する。 -/
theorem Circuit.controlledRyMacroExpansion_operator {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.controlledRyMacroExpansion control target different angle) =
      embedControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) := by
  simp only [Circuit.controlledRyMacroExpansion, Circuit.fromList,
    Circuit.denote, primitiveGateOperatorWithSymbols, Circuit.halfAngle,
    AngleExpr.eval, AngleExpr.uniformValue, Matrix.one_mul]
  rw [show deterministicOperator (fun input => xorWire target (input control) input) =
      analyticCnotOperator control target by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot control target different]
  rw [← embedTwoQubitOperator_localOnTarget control target different,
    ← embedTwoQubitOperator_localOnTarget control target different]
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
    ← embedTwoQubitOperator_mul]
  norm_num
  unfold embedControlledSingleQubitOperator
  apply congrArg (embedTwoQubitOperator control target different)
  rw [show -(AngleExpr.eval (fun _ => 0) angle / 2) =
      -AngleExpr.eval (fun _ => 0) angle / 2 by ring]
  exact local_controlledRy_decomposition
    (AngleExpr.eval (fun _ => 0) angle)

/-- 一制御Ry分解の行列要素はtargetの二項局所式である。 -/
theorem Circuit.controlledRyMacroExpansion_apply_sparse {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) (output input : QubitBasis qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.controlledRyMacroExpansion control target different angle)
        output input =
      if agreesExcept target output input then
        if input control then
          localRy angle.uniformValue (output target) (input target)
        else if output target = input target then 1 else 0
      else 0 := by
  rw [Circuit.controlledRyMacroExpansion_operator]
  unfold embedControlledSingleQubitOperator
  rw [embedTwoQubitOperator_apply]
  by_cases outside : agreesExceptTwo control target output input
  · by_cases controlEqual : output control = input control
    · have targetAgreement : agreesExcept target output input := by
        intro wire wireDifferent
        by_cases isControl : wire = control
        · simpa [isControl] using controlEqual
        · exact outside wire isControl wireDifferent
      simp [outside, localControlledOperator, targetAgreement, controlEqual]
    · have notTargetAgreement : ¬agreesExcept target output input := by
        intro agreement
        exact controlEqual (agreement control different)
      simp [outside, localControlledOperator, notTargetAgreement, controlEqual]
  · have notTargetAgreement : ¬agreesExcept target output input := by
      intro agreement
      apply outside
      intro wire firstDifferent secondDifferent
      exact agreement wire secondDifferent
    simp [outside, notTargetAgreement]

/-- 正制御列が成立したときだけ`Ry`となる疎な理想行列要素。 -/
def positiveControlledRyAmplitude
    {qubits : Nat}
    (controls : List (Fin qubits))
    (target : Fin qubits)
    (angle : ℝ)
    (output input : QubitBasis qubits) : ℂ :=
  if agreesExcept target output input then
    if ReversibleCircuit.allWiresTrue controls input then
      localRy angle (output target) (input target)
    else if output target = input target then 1 else 0
  else 0

/-- 正制御多重`Ry`の先頭ANDを計算した後に使う内部回路。 -/
def positiveMultiControlledRyUse
    {qubits : Nat}
    (scratch : Fin qubits)
    (controls scratches : List (Fin qubits))
    (target : Fin qubits) (angle : AngleExpr) :
    Circuit (PrimitiveGate qubits) :=
  match controls with
  | [] =>
      if different : scratch ≠ target then
        Circuit.controlledRyMacroExpansion scratch target different angle
      else .identity
  | _ :: _ => Circuit.andChainControlledRy scratch controls scratches target angle

/-- `positiveMultiControlledRy`内の二引数matchは内部use回路に一致する。 -/
theorem positiveMultiControlledRyUse_eq_match
    {qubits : Nat}
    (scratch : Fin qubits)
    (controls scratches : List (Fin qubits))
    (target : Fin qubits) (angle : AngleExpr) :
    (match controls, scratches with
    | [], _ =>
        if different : scratch ≠ target then
          Circuit.controlledRyMacroExpansion scratch target different angle
        else .identity
    | _, _ => Circuit.andChainControlledRy scratch controls scratches target angle) =
      positiveMultiControlledRyUse scratch controls scratches target angle := by
  cases controls <;> rfl

/-- 二本以上の制御では先頭Toffoli・内部use・先頭Toffoliの順になる。 -/
theorem positiveMultiControlledRy_cons_cons
    {qubits : Nat}
    (control₁ control₂ scratch : Fin qubits)
    (controls scratches : List (Fin qubits))
    (target : Fin qubits) (angle : AngleExpr) :
    Circuit.positiveMultiControlledRy
        (control₁ :: control₂ :: controls) (scratch :: scratches) target angle =
      .seq (Circuit.safeToffoli control₁ control₂ scratch)
        (.seq (positiveMultiControlledRyUse scratch controls scratches target angle)
          (Circuit.safeToffoli control₁ control₂ scratch)) := by
  cases controls <;> rfl

/-- Toffoliが量子target以外だけに作用すると、target外一致条件を保存する。 -/
theorem sameOutside_toffoliBasisAction_iff
    {qubits : Nat}
    (control₁ control₂ scratch target : Fin qubits)
    (firstDifferentScratch : control₁ ≠ scratch)
    (secondDifferentScratch : control₂ ≠ scratch)
    (firstDifferentTarget : control₁ ≠ target)
    (secondDifferentTarget : control₂ ≠ target)
    (scratchDifferentTarget : scratch ≠ target)
    (output input : QubitBasis qubits) :
    agreesExcept target
        (toffoliBasisAction control₁ control₂ scratch output)
        (toffoliBasisAction control₁ control₂ scratch input) ↔
      agreesExcept target output input := by
  have forward : ∀ left right : QubitBasis qubits,
      agreesExcept target left right →
        agreesExcept target
          (toffoliBasisAction control₁ control₂ scratch left)
          (toffoliBasisAction control₁ control₂ scratch right) := by
    intro left right same wire wireDifferentTarget
    by_cases isScratch : wire = scratch
    · subst wire
      have firstEqual := same control₁ firstDifferentTarget
      have secondEqual := same control₂ secondDifferentTarget
      have scratchEqual := same scratch scratchDifferentTarget
      simp [toffoliBasisAction, xorWire, firstEqual, secondEqual, scratchEqual]
    · simp [toffoliBasisAction, xorWire, isScratch,
        same wire wireDifferentTarget]
  constructor
  · intro transformed
    have twice := forward
      (toffoliBasisAction control₁ control₂ scratch output)
      (toffoliBasisAction control₁ control₂ scratch input) transformed
    simpa [toffoliBasisAction_involutive control₁ control₂ scratch
      firstDifferentScratch secondDifferentScratch] using twice
  · exact forward output input

/-- Toffoli targetと量子targetが異なれば量子targetのbit値は変わらない。 -/
@[simp] theorem toffoliBasisAction_quantumTarget
    {qubits : Nat}
    (control₁ control₂ scratch target : Fin qubits)
    (different : target ≠ scratch)
    (input : QubitBasis qubits) :
    toffoliBasisAction control₁ control₂ scratch input target = input target := by
  exact ReversibleCircuit.toffoliBasisAction_other
    control₁ control₂ scratch target different input

/-- 型安全なToffoli constructorは相異性証明下で指定Toffoli置換行列を表す。 -/
theorem safeToffoli_operator
    {qubits : Nat}
    (control₁ control₂ target : Fin qubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) :
    VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.safeToffoli control₁ control₂ target) =
      (toffoliBasisEquiv control₁ control₂ target
        firstDifferent secondDifferent).permMatrix ℂ := by
  simp [Circuit.safeToffoli, controlsDifferent, firstDifferent, secondDifferent,
    VerifiedCircuitCore.Circuit.denote, primitiveGateOperatorWithSymbols]
  exact deterministicOperator_toffoliBasisAction_eq_permMatrix
    control₁ control₂ target firstDifferent secondDifferent

/-- AND鎖内部のcontrolled-`Ry`はclean scratch上で全制御の論理積を実現する。 -/
theorem andChainControlledRy_apply_sparse
    {qubits : Nat}
    (previous : Fin qubits)
    (controls scratches : List (Fin qubits))
    (target : Fin qubits)
    (angle : AngleExpr)
    (output input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length)
    (layoutNodup : (previous :: controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.andChainControlledRy previous controls scratches target angle)
        output input =
      positiveControlledRyAmplitude (previous :: controls) target angle.uniformValue
        output input := by
  induction controls generalizing previous scratches output input with
  | nil =>
      have previousDifferentTarget : previous ≠ target := by
        intro equal
        apply (List.nodup_cons.mp layoutNodup).1
        simp [equal]
      simp only [Circuit.andChainControlledRy]
      simp [previousDifferentTarget,
        Circuit.controlledRyMacroExpansion_apply_sparse, positiveControlledRyAmplitude,
        ReversibleCircuit.allWiresTrue, ReversibleCircuit.readWires]
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
          have previousDifferentTarget : previous ≠ target := by
            intro equal
            apply previousFresh
            simp [equal]
          have controlDifferentTarget : control ≠ target := by
            intro equal
            apply controlFresh
            simp [equal]
          have recursiveLayout :
              (scratch :: controls ++ scratches ++ [target]).Nodup := by
            have permutation :=
              ReversibleCircuit.perm_cons_append scratch controls (scratches ++ [target])
            have reordered :
                (scratch :: controls ++ (scratches ++ [target])).Nodup := by
              apply permutation.symm.nodup
              simpa [List.append_assoc] using remainingNodup
            simpa [List.append_assoc] using reordered
          have scratchFresh := (List.nodup_cons.mp recursiveLayout).1
          have scratchDifferentTarget : scratch ≠ target := by
            intro equal
            apply scratchFresh
            simp [equal]
          have scratchZeroHead : input scratch = false := scratchZero scratch (by simp)
          let firstInput := toffoliBasisAction previous control scratch input
          let firstOutput := toffoliBasisAction previous control scratch output
          have scratchesStillZero : ∀ wire ∈ scratches, firstInput wire = false := by
            intro wire member
            dsimp [firstInput]
            rw [ReversibleCircuit.toffoliBasisAction_other previous control scratch wire]
            · exact scratchZero wire (by simp [member])
            · intro equal
              apply scratchFresh
              rw [← equal]
              simp [member]
          have controlsUnchanged :
              ReversibleCircuit.readWires controls firstInput =
                ReversibleCircuit.readWires controls input := by
            exact ReversibleCircuit.readWires_toffoliBasisAction_of_not_mem
              controls previous control scratch input (by
                intro member
                exact scratchFresh (by simp [member]))
          have allControlsUnchanged :
              (List.map firstInput controls).all id =
                (List.map input controls).all id := by
            simpa [ReversibleCircuit.readWires] using
              congrArg (fun values => values.all id) controlsUnchanged
          have recursiveCondition :
              ReversibleCircuit.allWiresTrue (scratch :: controls) firstInput =
                ReversibleCircuit.allWiresTrue (previous :: control :: controls) input := by
            unfold ReversibleCircuit.allWiresTrue
            simp only [ReversibleCircuit.readWires, List.map_cons, List.all_cons, id_eq]
            rw [allControlsUnchanged]
            rw [show firstInput scratch = (input previous && input control) by
              simp [firstInput, toffoliBasisAction, xorWire, scratchZeroHead]]
            exact Bool.and_assoc _ _ _
          have tailEnough : controls.length ≤ scratches.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using enoughScratch
          let permutation := toffoliBasisEquiv previous control scratch
            previousDifferentScratch controlDifferentScratch
          have involutive : permutation.symm = permutation := rfl
          simp only [Circuit.andChainControlledRy]
          change (VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) _)
              output input = _
          rw [VerifiedCircuitCore.Circuit.denote_seq,
            VerifiedCircuitCore.Circuit.denote_seq]
          rw [safeToffoli_operator previous control scratch previousDifferentControl
            previousDifferentScratch controlDifferentScratch]
          change (permutation.permMatrix ℂ *
              VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (Circuit.andChainControlledRy scratch controls scratches target angle) *
              permutation.permMatrix ℂ) output input = _
          rw [permMatrix_conjugate_operator_apply permutation involutive]
          change
            VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (Circuit.andChainControlledRy scratch controls scratches target angle)
                firstOutput firstInput = _
          rw [inductionHypothesis scratch scratches firstOutput firstInput tailEnough
            recursiveLayout scratchesStillZero]
          unfold positiveControlledRyAmplitude
          dsimp [firstOutput, firstInput]
          simp only [sameOutside_toffoliBasisAction_iff previous control scratch target
            previousDifferentScratch controlDifferentScratch
            previousDifferentTarget controlDifferentTarget scratchDifferentTarget]
          rw [recursiveCondition]
          simp only [toffoliBasisAction_quantumTarget previous control scratch target
            scratchDifferentTarget.symm output,
            toffoliBasisAction_quantumTarget previous control scratch target
              scratchDifferentTarget.symm input]

/-- 正制御多重`Ry`の基本ゲート回路はclean scratch上で疎な理想作用に一致する。 -/
theorem positiveMultiControlledRy_apply_sparse
    {qubits : Nat}
    (controls scratches : List (Fin qubits))
    (target : Fin qubits)
    (angle : AngleExpr)
    (output input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.positiveMultiControlledRy controls scratches target angle)
        output input =
      positiveControlledRyAmplitude controls target angle.uniformValue output input := by
  cases controls with
  | nil =>
      simp [Circuit.positiveMultiControlledRy,
        VerifiedCircuitCore.Circuit.denote,
        primitiveGateOperatorWithSymbols, embedSingleQubitOperator_apply,
        positiveControlledRyAmplitude, AngleExpr.uniformValue,
        ReversibleCircuit.allWiresTrue, ReversibleCircuit.readWires]
  | cons control controls =>
      cases controls with
      | nil =>
          have controlDifferentTarget : control ≠ target := by
            intro equal
            have fresh := (List.nodup_cons.mp layoutNodup).1
            apply fresh
            simp [equal]
          simp [Circuit.positiveMultiControlledRy, controlDifferentTarget,
            Circuit.controlledRyMacroExpansion_apply_sparse, positiveControlledRyAmplitude,
            ReversibleCircuit.allWiresTrue, ReversibleCircuit.readWires]
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
              have firstDifferentTarget : control ≠ target := by
                intro equal
                apply firstFresh
                simp [equal]
              have secondDifferentTarget : control₂ ≠ target := by
                intro equal
                apply secondFresh
                simp [equal]
              have recursiveLayout :
                  (scratch :: controls ++ scratches ++ [target]).Nodup := by
                have permutation :=
                  ReversibleCircuit.perm_cons_append scratch controls
                    (scratches ++ [target])
                have reordered :
                    (scratch :: controls ++ (scratches ++ [target])).Nodup := by
                  apply permutation.symm.nodup
                  simpa [List.append_assoc] using remainingNodup
                simpa [List.append_assoc] using reordered
              have scratchFresh := (List.nodup_cons.mp recursiveLayout).1
              have scratchDifferentTarget : scratch ≠ target := by
                intro equal
                apply scratchFresh
                simp [equal]
              have scratchZeroHead : input scratch = false :=
                scratchZero scratch (by simp)
              let firstInput := toffoliBasisAction control control₂ scratch input
              let firstOutput := toffoliBasisAction control control₂ scratch output
              have scratchesStillZero :
                  ∀ wire ∈ scratches, firstInput wire = false := by
                intro wire member
                dsimp [firstInput]
                rw [ReversibleCircuit.toffoliBasisAction_other
                  control control₂ scratch wire]
                · exact scratchZero wire (by simp [member])
                · intro equal
                  apply scratchFresh
                  rw [← equal]
                  simp [member]
              have controlsUnchanged :
                  ReversibleCircuit.readWires controls firstInput =
                    ReversibleCircuit.readWires controls input := by
                exact ReversibleCircuit.readWires_toffoliBasisAction_of_not_mem
                  controls control control₂ scratch input (by
                    intro member
                    exact scratchFresh (by simp [member]))
              have allControlsUnchanged :
                  (List.map firstInput controls).all id =
                    (List.map input controls).all id := by
                simpa [ReversibleCircuit.readWires] using
                  congrArg (fun values => values.all id) controlsUnchanged
              have recursiveCondition :
                  ReversibleCircuit.allWiresTrue (scratch :: controls) firstInput =
                    ReversibleCircuit.allWiresTrue
                      (control :: control₂ :: controls) input := by
                unfold ReversibleCircuit.allWiresTrue
                simp only [ReversibleCircuit.readWires, List.map_cons,
                  List.all_cons, id_eq]
                rw [allControlsUnchanged]
                rw [show firstInput scratch = (input control && input control₂) by
                  simp [firstInput, toffoliBasisAction, xorWire, scratchZeroHead]]
                exact Bool.and_assoc _ _ _
              have tailEnough : controls.length ≤ scratches.length := by
                simp only [List.length_cons] at enoughScratch
                omega
              let useCircuit : Circuit (PrimitiveGate qubits) :=
                positiveMultiControlledRyUse scratch controls scratches target angle
              have useSparse :
                  VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) useCircuit
                      firstOutput firstInput =
                    positiveControlledRyAmplitude (scratch :: controls) target
                      angle.uniformValue firstOutput firstInput := by
                cases controls with
                | nil =>
                    dsimp [useCircuit, positiveMultiControlledRyUse]
                    simp [scratchDifferentTarget,
                      Circuit.controlledRyMacroExpansion_apply_sparse,
                      positiveControlledRyAmplitude,
                      ReversibleCircuit.allWiresTrue,
                      ReversibleCircuit.readWires]
                | cons next rest =>
                    dsimp [useCircuit, positiveMultiControlledRyUse]
                    exact andChainControlledRy_apply_sparse scratch (next :: rest)
                      scratches target angle firstOutput firstInput tailEnough
                      recursiveLayout scratchesStillZero
              let permutation := toffoliBasisEquiv control control₂ scratch
                firstDifferentScratch secondDifferentScratch
              have involutive : permutation.symm = permutation := rfl
              rw [positiveMultiControlledRy_cons_cons]
              change (VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                  (.seq (Circuit.safeToffoli control control₂ scratch)
                    (.seq useCircuit (Circuit.safeToffoli control control₂ scratch))))
                    output input = _
              rw [VerifiedCircuitCore.Circuit.denote_seq,
                VerifiedCircuitCore.Circuit.denote_seq]
              rw [safeToffoli_operator control control₂ scratch controlsDifferent
                firstDifferentScratch secondDifferentScratch]
              change (permutation.permMatrix ℂ *
                  VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) useCircuit *
                  permutation.permMatrix ℂ) output input = _
              rw [permMatrix_conjugate_operator_apply permutation involutive]
              change VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) useCircuit
                  firstOutput firstInput = _
              rw [useSparse]
              unfold positiveControlledRyAmplitude
              dsimp [firstOutput, firstInput]
              simp only [sameOutside_toffoliBasisAction_iff
                control control₂ scratch target
                firstDifferentScratch secondDifferentScratch firstDifferentTarget
                secondDifferentTarget scratchDifferentTarget]
              rw [recursiveCondition]
              simp only [toffoliBasisAction_quantumTarget control control₂ scratch target
                scratchDifferentTarget.symm output,
                toffoliBasisAction_quantumTarget control control₂ scratch target
                  scratchDifferentTarget.symm input]

end

end VerifiedCircuitCore
