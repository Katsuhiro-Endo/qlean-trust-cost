import QLean.Generator.Implementation.UniformPreparationCircuit
import QLean.Generator.Implementation.CoreCircuitEmbeddingSemantics
import QLean.Generator.Implementation.PrimitiveCoreSemanticsAdapter
import QLean.Generator.Implementation.LayoutCorrectness
import QLean.Generator.Analysis.SharedUniformPreparationFullOperator
import QLean.Circuits.Foundation.UniformPreparationCorrectness
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.ControlledRotationMacros

/-!
# 共有一様準備componentのQレイアウトadapter

共有coreが証明した局所幅`2w`の一様準備componentを、Q回路のselector sliceと
AND work sliceの先頭`w`本へ型安全に配置する。ここでは凍結Q ASTとの一致は主張せず、
共有componentを任意のQ背景基底へ持ち上げるwire/layout境界だけを与える。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/--
共有一様準備compilerが生成し得るcore角度をQ記号角度へ構文的に移す。
一様準備に現れない`const`、`symbol`、一般商は0へ退避する。
-/
def representableCoreAngleToQ : VerifiedCircuitCore.AngleExpr → AngleExpr
  | .const _ => .rational 0
  | .rational numerator denominator _ =>
      .rational ((numerator : ℚ) / (denominator : ℚ))
  | .decimal mantissa scale =>
      .rational ((mantissa : ℚ) / (10 : ℚ) ^ scale)
  | .symbol _ => .rational 0
  | .pi => .pi
  | .add left right =>
      .add (representableCoreAngleToQ left) (representableCoreAngleToQ right)
  | .mul left right =>
      .mul (representableCoreAngleToQ left) (representableCoreAngleToQ right)
  | .div left (.rational 2 1 _) =>
      (representableCoreAngleToQ left).half
  | .div _ _ => .rational 0
  | .neg value => .neg (representableCoreAngleToQ value)
  | .sqrt value => .sqrt (representableCoreAngleToQ value)
  | .acos value => .acos (representableCoreAngleToQ value)

/-- core角度の構文変換が実数意味論を保存するというrestricted compiler境界。 -/
def CoreAngleRepresentable (angle : VerifiedCircuitCore.AngleExpr) : Prop :=
  (representableCoreAngleToQ angle).toReal = angle.eval (fun _ => 0)

/-- 共有coreの分岐角度を構文変換すると既存Q分岐角度へ一致する。 -/
theorem representableCoreAngleToQ_uniformSplitAngle (left right : Nat) :
    representableCoreAngleToQ
        (VerifiedCircuitCore.uniformSplitAngle left right) =
      uniformSplitAngle left right := by
  by_cases positive : 0 < left + right
  · simp [VerifiedCircuitCore.uniformSplitAngle, uniformSplitAngle,
      positive, representableCoreAngleToQ, AngleExpr.twice]
  · have zero : left + right = 0 := Nat.eq_zero_of_not_pos positive
    simp [VerifiedCircuitCore.uniformSplitAngle, uniformSplitAngle,
      zero, representableCoreAngleToQ]

/-- 共有coreの半角構文を変換すると既存Q半角構文へ一致する。 -/
theorem representableCoreAngleToQ_halfAngle
    (angle : VerifiedCircuitCore.AngleExpr) :
    representableCoreAngleToQ
        (VerifiedCircuitCore.Circuit.halfAngle angle) =
      (representableCoreAngleToQ angle).half := by
  simp [VerifiedCircuitCore.Circuit.halfAngle,
    representableCoreAngleToQ]

/-- 共有core一様回転命令を既存Q命令構文へ決定的に移す。 -/
def coreUniformRotationInstructionToQ
    (instruction : VerifiedCircuitCore.UniformRotationInstruction) :
    UniformRotationInstruction where
  target := instruction.target
  controls := instruction.controls
  angle := representableCoreAngleToQ instruction.angle

/-- 命令変換は最高位制御の追加と可換である。 -/
theorem coreUniformRotationInstructionToQ_addControl
    (width : Nat) (expected : Bool)
    (instruction : VerifiedCircuitCore.UniformRotationInstruction) :
    coreUniformRotationInstructionToQ
        { instruction with
          controls := (width, expected) :: instruction.controls } =
      { coreUniformRotationInstructionToQ instruction with
        controls := (width, expected) :: instruction.controls } := by
  rfl

/-- 共有coreと既存Qの生一様回転計画は命令構文変換で完全一致する。 -/
theorem coreUniformRotationPlan_map_toQ (width validCount : Nat) :
    (VerifiedCircuitCore.uniformRotationPlan width validCount).map
        coreUniformRotationInstructionToQ =
      uniformRotationPlan width validCount := by
  induction width generalizing validCount with
  | zero =>
      simp only [VerifiedCircuitCore.uniformRotationPlan,
        uniformRotationPlan, List.map_nil]
  | succ width inductionHypothesis =>
      by_cases zero : validCount = 0
      · simp [VerifiedCircuitCore.uniformRotationPlan, zero]
      · rw [VerifiedCircuitCore.uniformRotationPlan, uniformRotationPlan]
        rw [dif_neg zero, dif_neg zero]
        simp only [List.map_cons, List.map_append]
        congr 1
        · simp [coreUniformRotationInstructionToQ,
            representableCoreAngleToQ_uniformSplitAngle]
        · apply congrArg₂ (· ++ ·)
          · rw [List.map_map]
            have mapFunction :
                coreUniformRotationInstructionToQ ∘
                    (fun instruction :
                      VerifiedCircuitCore.UniformRotationInstruction =>
                        { instruction with controls :=
                          (width, false) :: instruction.controls }) =
                  (fun instruction : UniformRotationInstruction =>
                    { instruction with controls :=
                      (width, false) :: instruction.controls }) ∘
                    coreUniformRotationInstructionToQ := by
              funext instruction
              exact coreUniformRotationInstructionToQ_addControl
                width false instruction
            rw [mapFunction, ← List.map_map, inductionHypothesis]
          · rw [List.map_map]
            have mapFunction :
                coreUniformRotationInstructionToQ ∘
                    (fun instruction :
                      VerifiedCircuitCore.UniformRotationInstruction =>
                        { instruction with controls :=
                          (width, true) :: instruction.controls }) =
                  (fun instruction : UniformRotationInstruction =>
                    { instruction with controls :=
                      (width, true) :: instruction.controls }) ∘
                    coreUniformRotationInstructionToQ := by
              funext instruction
              exact coreUniformRotationInstructionToQ_addControl
                width true instruction
            rw [mapFunction, ← List.map_map, inductionHypothesis]

/-- core命令のwell-formed証明はQ命令変換後もそのまま成立する。 -/
theorem coreUniformRotationInstructionToQ_wellFormed
    {width : Nat}
    (instruction : VerifiedCircuitCore.UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    (coreUniformRotationInstructionToQ instruction).WellFormed width := by
  simpa [VerifiedCircuitCore.UniformRotationInstruction.WellFormed,
    UniformRotationInstruction.WellFormed,
    coreUniformRotationInstructionToQ] using wellFormed

/-- 証明付きcore命令を証明付きQ命令へ移す。 -/
def coreAttachedUniformRotationInstructionToQ
    {width : Nat}
    (instruction : {instruction : VerifiedCircuitCore.UniformRotationInstruction //
      instruction.WellFormed width}) :
    {instruction : UniformRotationInstruction //
      instruction.WellFormed width} :=
  ⟨coreUniformRotationInstructionToQ instruction.1,
    coreUniformRotationInstructionToQ_wellFormed instruction.1 instruction.2⟩

/-- 証明付き根命令の変換は既存Q根命令へ一致する。 -/
theorem coreAttachedUniformRootInstructionToQ
    (width validCount : Nat) :
    coreAttachedUniformRotationInstructionToQ
        (VerifiedCircuitCore.attachedUniformRootInstruction width validCount) =
      attachedUniformRootInstruction width validCount := by
  apply Subtype.ext
  simp [coreAttachedUniformRotationInstructionToQ,
    coreUniformRotationInstructionToQ,
    VerifiedCircuitCore.attachedUniformRootInstruction,
    VerifiedCircuitCore.uniformRootInstruction,
    attachedUniformRootInstruction, uniformRootInstruction,
    representableCoreAngleToQ_uniformSplitAngle]
  simp only [VerifiedCircuitCore.uniformLeftCount,
    VerifiedCircuitCore.uniformRightCount, uniformLeftCount,
    uniformRightCount]

/-- 証明付き命令変換は最高位制御追加と可換である。 -/
theorem coreAttachedUniformRotationInstructionToQ_addHighestControl
    {width : Nat} (expected : Bool)
    (instruction : {instruction : VerifiedCircuitCore.UniformRotationInstruction //
      instruction.WellFormed width}) :
    coreAttachedUniformRotationInstructionToQ
        (VerifiedCircuitCore.addHighestControlInstruction expected instruction) =
      addHighestControlInstruction expected
        (coreAttachedUniformRotationInstructionToQ instruction) := by
  apply Subtype.ext
  exact coreUniformRotationInstructionToQ_addControl
    width expected instruction.1

/-- 共有coreと既存Qの証明付き一様回転計画も完全一致する。 -/
theorem coreAttachedUniformRotationPlan_map_toQ
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width) :
    (VerifiedCircuitCore.attachedUniformRotationPlan
      width validCount capacity).map
        coreAttachedUniformRotationInstructionToQ =
      attachedUniformRotationPlan width validCount capacity := by
  induction width generalizing validCount with
  | zero =>
      simp only [VerifiedCircuitCore.attachedUniformRotationPlan,
        attachedUniformRotationPlan, List.map_nil]
  | succ width inductionHypothesis =>
      by_cases zero : validCount = 0
      · simp [VerifiedCircuitCore.attachedUniformRotationPlan,
          attachedUniformRotationPlan, zero]
      · rw [VerifiedCircuitCore.attachedUniformRotationPlan,
          attachedUniformRotationPlan]
        rw [dif_neg zero, dif_neg zero]
        simp only [List.map_cons, List.map_append]
        congr 1
        · exact coreAttachedUniformRootInstructionToQ width validCount
        · apply congrArg₂ (· ++ ·)
          · unfold VerifiedCircuitCore.addHighestControlInstructions
              addHighestControlInstructions
            rw [List.map_map]
            have mapFunction :
                (coreAttachedUniformRotationInstructionToQ
                    (width := width + 1)) ∘
                    (VerifiedCircuitCore.addHighestControlInstruction
                      (width := width) false) =
                  (addHighestControlInstruction (width := width) false) ∘
                    (coreAttachedUniformRotationInstructionToQ
                      (width := width)) := by
              funext instruction
              exact
                coreAttachedUniformRotationInstructionToQ_addHighestControl
                  false instruction
            change
              List.map
                  ((coreAttachedUniformRotationInstructionToQ
                      (width := width + 1)) ∘
                    (VerifiedCircuitCore.addHighestControlInstruction
                      (width := width) false))
                  (VerifiedCircuitCore.attachedUniformRotationPlan width
                    (VerifiedCircuitCore.uniformLeftCount width validCount) _) =
                List.map
                  (addHighestControlInstruction (width := width) false)
                  (attachedUniformRotationPlan width
                    (uniformLeftCount width validCount) _)
            rw [mapFunction, ← List.map_map]
            simpa [List.map_map, VerifiedCircuitCore.uniformLeftCount,
              uniformLeftCount] using
              congrArg
                (List.map
                  (addHighestControlInstruction (width := width) false))
                (inductionHypothesis (min validCount (2 ^ width))
                  (VerifiedCircuitCore.uniformLeftCount_le_capacity
                    width validCount))
          · unfold VerifiedCircuitCore.addHighestControlInstructions
              addHighestControlInstructions
            rw [List.map_map]
            have mapFunction :
                (coreAttachedUniformRotationInstructionToQ
                    (width := width + 1)) ∘
                    (VerifiedCircuitCore.addHighestControlInstruction
                      (width := width) true) =
                  (addHighestControlInstruction (width := width) true) ∘
                    (coreAttachedUniformRotationInstructionToQ
                      (width := width)) := by
              funext instruction
              exact
                coreAttachedUniformRotationInstructionToQ_addHighestControl
                  true instruction
            change
              List.map
                  ((coreAttachedUniformRotationInstructionToQ
                      (width := width + 1)) ∘
                    (VerifiedCircuitCore.addHighestControlInstruction
                      (width := width) true))
                  (VerifiedCircuitCore.attachedUniformRotationPlan width
                    (VerifiedCircuitCore.uniformRightCount width validCount) _) =
                List.map
                  (addHighestControlInstruction (width := width) true)
                  (attachedUniformRotationPlan width
                    (uniformRightCount width validCount) _)
            rw [mapFunction, ← List.map_map]
            simpa [List.map_map, VerifiedCircuitCore.uniformRightCount,
              VerifiedCircuitCore.uniformLeftCount,
              uniformRightCount, uniformLeftCount] using
              congrArg
                (List.map
                  (addHighestControlInstruction (width := width) true))
                (inductionHypothesis
                  (validCount - min validCount (2 ^ width))
                  (VerifiedCircuitCore.uniformRightCount_le_capacity
                    width validCount capacity))

/-- 表現可能な角度では構文変換後のQ角度の実数意味論がcore角度と一致する。 -/
theorem representableCoreAngleToQ_toReal
    (angle : VerifiedCircuitCore.AngleExpr)
    (represented : CoreAngleRepresentable angle) :
    (representableCoreAngleToQ angle).toReal = angle.eval (fun _ => 0) := by
  exact represented

/-- 一様準備木の分岐角度はQ記号角度で表現可能である。 -/
theorem coreUniformSplitAngle_representable (left right : Nat) :
    CoreAngleRepresentable (VerifiedCircuitCore.uniformSplitAngle left right) := by
  unfold CoreAngleRepresentable
  rw [representableCoreAngleToQ_uniformSplitAngle]
  by_cases positive : 0 < left + right
  · rw [uniformSplitAngle_toReal left right positive]
    rw [VerifiedCircuitCore.uniformSplitAngle_eval (fun _ => 0)
      left right positive]
  · have zero : left + right = 0 := Nat.eq_zero_of_not_pos positive
    simp [uniformSplitAngle, VerifiedCircuitCore.uniformSplitAngle,
      zero, AngleExpr.toReal, VerifiedCircuitCore.AngleExpr.eval]

/-- 表現可能角度の半角もQ記号角度で表現可能である。 -/
theorem coreHalfAngle_representable
    {angle : VerifiedCircuitCore.AngleExpr}
    (represented : CoreAngleRepresentable angle) :
    CoreAngleRepresentable (VerifiedCircuitCore.Circuit.halfAngle angle) := by
  unfold CoreAngleRepresentable
  unfold CoreAngleRepresentable at represented
  rw [representableCoreAngleToQ_halfAngle]
  rw [AngleExpr.toReal_half]
  simp only [VerifiedCircuitCore.Circuit.halfAngle,
    VerifiedCircuitCore.AngleExpr.eval]
  rw [represented]
  norm_num

/-- 表現可能角度の符号反転もQ記号角度で表現可能である。 -/
theorem coreNegAngle_representable
    {angle : VerifiedCircuitCore.AngleExpr}
    (represented : CoreAngleRepresentable angle) :
    CoreAngleRepresentable (.neg angle) := by
  change -(representableCoreAngleToQ angle).toReal =
    -(angle.eval (fun _ => 0))
  rw [represented]

/-- restricted compilerが意味を厳密に保存できる共有core gateの局所条件。 -/
def SharedUniformGateCompilable {qubits : Nat}
    (gate : VerifiedCircuitCore.PrimitiveGate qubits) : Prop :=
  match gate with
  | .x _ | .h _ | .cnot _ _ _ | .toffoli _ _ _ _ _ _ => True
  | .ry angle _ => CoreAngleRepresentable angle
  | _ => False

/-- 回路の全leafがrestricted compilerの局所条件を満たす。 -/
def SharedUniformCircuitCompilable {qubits : Nat}
    (circuit : VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits)) : Prop :=
  ∀ gate, gate ∈ circuit.flatten → SharedUniformGateCompilable gate

/-- 空回路にはcompiler条件を破るleafがない。 -/
theorem sharedUniformCircuitCompilable_identity {qubits : Nat} :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.identity :
        VerifiedCircuitCore.Circuit
          (VerifiedCircuitCore.PrimitiveGate qubits)) := by
  simp [SharedUniformCircuitCompilable, VerifiedCircuitCore.Circuit.flatten]

/-- 局所条件を満たす一leaf回路も回路条件を満たす。 -/
theorem sharedUniformCircuitCompilable_gate
    {qubits : Nat} {gate : VerifiedCircuitCore.PrimitiveGate qubits}
    (compilable : SharedUniformGateCompilable gate) :
    SharedUniformCircuitCompilable (.gate gate) := by
  simpa [SharedUniformCircuitCompilable,
    VerifiedCircuitCore.Circuit.flatten] using compilable

/-- 二つのcompiler可能回路の逐次合成もcompiler可能である。 -/
theorem sharedUniformCircuitCompilable_seq
    {qubits : Nat}
    {first second : VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits)}
    (firstCompilable : SharedUniformCircuitCompilable first)
    (secondCompilable : SharedUniformCircuitCompilable second) :
    SharedUniformCircuitCompilable (.seq first second) := by
  intro gate member
  simp only [VerifiedCircuitCore.Circuit.flatten, List.mem_append] at member
  exact member.elim (firstCompilable gate) (secondCompilable gate)

/-- 型安全CNOT constructorの全leafはcompiler可能である。 -/
theorem safeCnot_sharedUniformCircuitCompilable
    {qubits : Nat} (control target : Fin qubits) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.safeCnot control target) := by
  unfold VerifiedCircuitCore.Circuit.safeCnot
  split
  · exact sharedUniformCircuitCompilable_gate trivial
  · exact sharedUniformCircuitCompilable_identity

/-- 型安全Toffoli constructorの全leafはcompiler可能である。 -/
theorem safeToffoli_sharedUniformCircuitCompilable
    {qubits : Nat} (control₀ control₁ target : Fin qubits) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.safeToffoli control₀ control₁ target) := by
  unfold VerifiedCircuitCore.Circuit.safeToffoli
  split
  · split
    · split
      · exact sharedUniformCircuitCompilable_gate trivial
      · exact sharedUniformCircuitCompilable_identity
    · exact sharedUniformCircuitCompilable_identity
  · exact sharedUniformCircuitCompilable_identity

/-- 一制御Ry分解の全角度leafは元角度から表現可能である。 -/
theorem controlledRyMacroExpansion_sharedUniformCircuitCompilable
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) (angle : VerifiedCircuitCore.AngleExpr)
    (represented : CoreAngleRepresentable angle) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.controlledRyMacroExpansion
        control target different angle) := by
  intro gate member
  simp only [VerifiedCircuitCore.Circuit.controlledRyMacroExpansion,
    VerifiedCircuitCore.Circuit.flatten_fromList, List.mem_cons] at member
  simp at member
  rcases member with member | member | member | member
  all_goals subst gate
  · exact coreHalfAngle_representable represented
  · trivial
  · exact coreNegAngle_representable
      (coreHalfAngle_representable represented)
  · trivial

/-- 零制御反転列のleafはすべてXである。 -/
theorem invertZeroControls_sharedUniformCircuitCompilable
    {qubits : Nat} (controls : List (Fin qubits × Bool)) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.invertZeroControls controls) := by
  intro gate member
  simp only [VerifiedCircuitCore.Circuit.invertZeroControls,
    VerifiedCircuitCore.Circuit.flatten_fromList] at member
  rcases List.mem_filterMap.mp member with
    ⟨control, controlMember, produced⟩
  by_cases enabled : control.2
  · simp [enabled] at produced
  · simp [enabled] at produced
    subst gate
    trivial

/-- 既計算ANDを延長する再帰回路の全leafはcompiler可能である。 -/
theorem andChainControlledRy_sharedUniformCircuitCompilable
    {qubits : Nat} (previous : Fin qubits)
    (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : VerifiedCircuitCore.AngleExpr)
    (represented : CoreAngleRepresentable angle) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.andChainControlledRy previous controls
        scratches target angle) := by
  induction controls generalizing previous scratches with
  | nil =>
      simp only [VerifiedCircuitCore.Circuit.andChainControlledRy]
      split
      · exact controlledRyMacroExpansion_sharedUniformCircuitCompilable
          previous target _ angle represented
      · exact sharedUniformCircuitCompilable_identity
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil =>
          simp [VerifiedCircuitCore.Circuit.andChainControlledRy,
            sharedUniformCircuitCompilable_identity]
      | cons scratch scratches =>
          simp only [VerifiedCircuitCore.Circuit.andChainControlledRy]
          exact sharedUniformCircuitCompilable_seq
            (safeToffoli_sharedUniformCircuitCompilable
              previous control scratch)
            (sharedUniformCircuitCompilable_seq
              (inductionHypothesis scratch scratches)
              (safeToffoli_sharedUniformCircuitCompilable
                previous control scratch))

/-- 正制御多重Ryの全leafはcompiler可能である。 -/
theorem positiveMultiControlledRy_sharedUniformCircuitCompilable
    {qubits : Nat} (controls scratches : List (Fin qubits))
    (target : Fin qubits) (angle : VerifiedCircuitCore.AngleExpr)
    (represented : CoreAngleRepresentable angle) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.positiveMultiControlledRy controls
        scratches target angle) := by
  cases controls with
  | nil =>
      exact sharedUniformCircuitCompilable_gate represented
  | cons control controls =>
      cases controls with
      | nil =>
          simp only [VerifiedCircuitCore.Circuit.positiveMultiControlledRy]
          split
          · exact controlledRyMacroExpansion_sharedUniformCircuitCompilable
              control target _ angle represented
          · exact sharedUniformCircuitCompilable_identity
      | cons control₁ controls =>
          cases scratches with
          | nil =>
              simp [VerifiedCircuitCore.Circuit.positiveMultiControlledRy,
                sharedUniformCircuitCompilable_identity]
          | cons scratch scratches =>
              simp only [VerifiedCircuitCore.Circuit.positiveMultiControlledRy]
              apply sharedUniformCircuitCompilable_seq
                (safeToffoli_sharedUniformCircuitCompilable
                  control control₁ scratch)
              apply sharedUniformCircuitCompilable_seq
              · cases controls with
                | nil =>
                    simp only
                    split
                    · exact controlledRyMacroExpansion_sharedUniformCircuitCompilable
                        scratch target _ angle represented
                    · exact sharedUniformCircuitCompilable_identity
                | cons next rest =>
                    exact andChainControlledRy_sharedUniformCircuitCompilable
                      scratch (next :: rest) scratches target angle represented
              · exact safeToffoli_sharedUniformCircuitCompilable
                  control control₁ scratch

/-- Bool多重制御Ryの全leafはcompiler可能である。 -/
theorem boolMultiControlledRy_sharedUniformCircuitCompilable
    {qubits : Nat} (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : VerifiedCircuitCore.AngleExpr)
    (represented : CoreAngleRepresentable angle) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.Circuit.boolMultiControlledRy controls scratches
        target angle) := by
  unfold VerifiedCircuitCore.Circuit.boolMultiControlledRy
  exact sharedUniformCircuitCompilable_seq
    (invertZeroControls_sharedUniformCircuitCompilable controls)
    (sharedUniformCircuitCompilable_seq
      (positiveMultiControlledRy_sharedUniformCircuitCompilable
        (controls.map Prod.fst) scratches target angle represented)
      (invertZeroControls_sharedUniformCircuitCompilable controls))

/-- 生の一様回転計画の各角度はQ記号角度で厳密に表現できる。 -/
theorem uniformRotationPlan_angle_representable (width validCount : Nat) :
    ∀ instruction ∈ VerifiedCircuitCore.uniformRotationPlan width validCount,
      CoreAngleRepresentable instruction.angle := by
  induction width generalizing validCount with
  | zero => simp [VerifiedCircuitCore.uniformRotationPlan]
  | succ width inductionHypothesis =>
      intro instruction member
      by_cases zero : validCount = 0
      · simp [VerifiedCircuitCore.uniformRotationPlan, zero] at member
      · simp only [VerifiedCircuitCore.uniformRotationPlan, dif_neg zero,
          List.mem_cons, List.mem_append, List.mem_map] at member
        rcases member with rfl | member | member
        · exact coreUniformSplitAngle_representable _ _
        · rcases member with ⟨source, sourceMember, rfl⟩
          exact inductionHypothesis _ source sourceMember
        · rcases member with ⟨source, sourceMember, rfl⟩
          exact inductionHypothesis _ source sourceMember

/-- 証明付き一様回転計画も各角度のQ記号表現可能性を保つ。 -/
theorem attachedUniformRotationPlan_angle_representable
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width) :
    ∀ instruction ∈ VerifiedCircuitCore.attachedUniformRotationPlan
        width validCount capacity,
      CoreAngleRepresentable instruction.1.angle := by
  intro instruction member
  apply uniformRotationPlan_angle_representable width validCount instruction.1
  rw [← VerifiedCircuitCore.attachedUniformRotationPlan_values
    width validCount capacity]
  exact List.mem_map.mpr ⟨instruction, member, rfl⟩

/-- 一個の一様回転命令をcompileした回路の全leafはcompiler可能である。 -/
theorem compileUniformRotationInstruction_sharedUniformCircuitCompilable
    (width : Nat) (instruction : VerifiedCircuitCore.UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width)
    (represented : CoreAngleRepresentable instruction.angle) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.compileUniformRotationInstruction
        width instruction wellFormed) := by
  exact boolMultiControlledRy_sharedUniformCircuitCompilable
    _ _ _ _ represented

/-- 共有一様準備正本の全leafはrestricted compilerで意味保存できる。 -/
theorem uniformPreparationCircuit_sharedUniformCircuitCompilable
    (parameters : VerifiedCircuitCore.UniformPreparationParameters) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.uniformPreparationCircuit parameters) := by
  intro gate member
  simp only [VerifiedCircuitCore.uniformPreparationCircuit,
    VerifiedCircuitCore.Circuit.flatten_sequence, List.mem_flatMap] at member
  rcases member with ⟨compiled, compiledMember, gateMember⟩
  rcases List.mem_map.mp compiledMember with
    ⟨instruction, instructionMember, rfl⟩
  exact compileUniformRotationInstruction_sharedUniformCircuitCompilable
    parameters.width instruction.1 instruction.2
      (attachedUniformRotationPlan_angle_representable _ _ _ instruction
        instructionMember) gate gateMember

/-- injective wire配置はrestricted compilerの局所条件を保存する。 -/
theorem primitiveGate_mapWires_sharedUniformGateCompilable
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (gate : VerifiedCircuitCore.PrimitiveGate sourceQubits)
    (compilable : SharedUniformGateCompilable gate) :
    SharedUniformGateCompilable
      (VerifiedCircuitCore.PrimitiveGate.mapWires placement gate) := by
  cases gate <;> simp_all [SharedUniformGateCompilable,
    VerifiedCircuitCore.PrimitiveGate.mapWires]

/--
共有core gateをQの許可基本ゲート回路へcompileする。uniform ASTに現れないgateは
identityへ退避し、正しさは`liftByCircuitCompiler`で実在leafだけに要求する。
-/
noncomputable def compileSharedUniformCoreGate
    {ancillaQubits systemQubits : Nat} :
    VerifiedCircuitCore.PrimitiveGate (ancillaQubits + systemQubits) →
      Circuit (PrimitiveGate ancillaQubits systemQubits)
  | .x target => .gate (.x (canonicalFinToWire target))
  | .h target => .gate (.h (canonicalFinToWire target))
  | .ry angle target =>
      .gate (.ry (canonicalFinToWire target)
        (representableCoreAngleToQ angle))
  | .cnot control target different =>
      .gate (.cnot (canonicalFinToWire control) (canonicalFinToWire target)
        (fun equal => different <| by
          simpa using congrArg wireToCanonicalFin equal))
  | .toffoli first second target controlsDifferent firstDifferent
      secondDifferent =>
      .gate (.toffoli (canonicalFinToWire first) (canonicalFinToWire second)
        (canonicalFinToWire target)
        (fun equal => controlsDifferent <| by
          simpa using congrArg wireToCanonicalFin equal)
        (fun equal => firstDifferent <| by
          simpa using congrArg wireToCanonicalFin equal)
        (fun equal => secondDifferent <| by
          simpa using congrArg wireToCanonicalFin equal))
  | _ => .identity

/-- Q primitive gateを標準Qubit基底上で解釈する。 -/
def qPrimitiveGateOperatorOnCanonicalCore
    {ancillaQubits systemQubits : Nat}
    (gate : PrimitiveGate ancillaQubits systemQubits) :
    VerifiedCircuitCore.Operator
      (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits)) :=
  reindexJointOperatorToCanonicalCore (primitiveGateOperator gate)

/-- restricted compilerは局所条件を満たす共有core gateの作用素を保存する。 -/
theorem compileSharedUniformCoreGate_correct
    {ancillaQubits systemQubits : Nat}
    (gate : VerifiedCircuitCore.PrimitiveGate
      (ancillaQubits + systemQubits))
    (compilable : SharedUniformGateCompilable gate) :
    VerifiedCircuitCore.Circuit.denote
        qPrimitiveGateOperatorOnCanonicalCore
        (compileSharedUniformCoreGate gate) =
      VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0) gate := by
  cases gate with
  | x target =>
      change reindexJointOperatorToCanonicalCore
          (primitiveGateOperator
            (PrimitiveGate.x (canonicalFinToWire target))) = _
      rw [← primitiveGate_toCanonicalCore_operator
        (PrimitiveGate.x (canonicalFinToWire target))]
      simp [PrimitiveGate.toCanonicalCore]
  | phaseShift _ _ => contradiction
  | h target =>
      change reindexJointOperatorToCanonicalCore
          (primitiveGateOperator
            (PrimitiveGate.h (canonicalFinToWire target))) = _
      rw [← primitiveGate_toCanonicalCore_operator
        (PrimitiveGate.h (canonicalFinToWire target))]
      simp [PrimitiveGate.toCanonicalCore,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols]
  | ry angle target =>
      change reindexJointOperatorToCanonicalCore
          (primitiveGateOperator
            (PrimitiveGate.ry (canonicalFinToWire target)
              (representableCoreAngleToQ angle))) = _
      rw [← primitiveGate_toCanonicalCore_operator
        (PrimitiveGate.ry (canonicalFinToWire target)
          (representableCoreAngleToQ angle))]
      simp [PrimitiveGate.toCanonicalCore, AngleExpr.toCore_eval,
        representableCoreAngleToQ_toReal angle compilable,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols]
  | cnot control target different =>
      change reindexJointOperatorToCanonicalCore
          (primitiveGateOperator
            (PrimitiveGate.cnot (canonicalFinToWire control)
              (canonicalFinToWire target) _)) = _
      rw [← primitiveGate_toCanonicalCore_operator
        (PrimitiveGate.cnot (canonicalFinToWire control)
          (canonicalFinToWire target) _)]
      simp [PrimitiveGate.toCanonicalCore]
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      change reindexJointOperatorToCanonicalCore
          (primitiveGateOperator
            (PrimitiveGate.toffoli (canonicalFinToWire control₀)
              (canonicalFinToWire control₁) (canonicalFinToWire target)
              _ _ _)) = _
      rw [← primitiveGate_toCanonicalCore_operator
        (PrimitiveGate.toffoli (canonicalFinToWire control₀)
          (canonicalFinToWire control₁) (canonicalFinToWire target)
          _ _ _)]
      simp [PrimitiveGate.toCanonicalCore]

/-- selector幅はQのAND work幅以下である。 -/
theorem selectorWidth_le_andWorkWidth (p : QParameters) :
    p.selectorWidth ≤ p.andWorkWidth := by
  simp [QParameters.andWorkWidth]
  omega

/-- 共有compilerの局所scratch indexをQのAND work sliceへ埋め込む。 -/
def sharedUniformScratchWire (p : QParameters) (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire
    ⟨index.val, lt_of_lt_of_le index.isLt (selectorWidth_le_andWorkWidth p)⟩

/-- 共有局所幅`2w`の前半をselector、後半をscratchへ写すQ wire配置。 -/
def sharedUniformLocalWire (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (index : Fin (2 * p.selectorWidth)) : Wire p.ancillaWidth p.systemWidth :=
  if selector : index.val < p.selectorWidth then
    selectorWire ⟨index.val, selector⟩
  else
    sharedUniformScratchWire p
      ⟨index.val - p.selectorWidth, by omega⟩

/-- 局所scratch wireは既存のQ一様準備scratch listに属する。 -/
theorem sharedUniformScratchWire_mem_uniformScratchWires
    (p : QParameters) (index : Fin p.selectorWidth) :
    sharedUniformScratchWire p index ∈ uniformScratchWires p := by
  unfold sharedUniformScratchWire uniformScratchWires
  apply List.mem_map.mpr
  refine ⟨⟨index.val, lt_of_lt_of_le index.isLt
    (selectorWidth_le_andWorkWidth p)⟩, List.mem_finRange _, rfl⟩

/-- selectorとQ一様準備scratchが互いに素なら、局所`2w`配置は単射である。 -/
theorem sharedUniformLocalWire_injective
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    Function.Injective (sharedUniformLocalWire p selectorWire) := by
  intro first second equal
  by_cases firstSelector : first.val < p.selectorWidth
  · by_cases secondSelector : second.val < p.selectorWidth
    · have selectorEqual :
          selectorWire ⟨first.val, firstSelector⟩ =
            selectorWire ⟨second.val, secondSelector⟩ := by
        simpa [sharedUniformLocalWire, firstSelector, secondSelector] using equal
      have indexEqual := selectorInjective selectorEqual
      have valueEqual : first.val = second.val :=
        congrArg (fun index : Fin p.selectorWidth => index.val) indexEqual
      exact Fin.ext valueEqual
    · exfalso
      have selectorMember :
          selectorWire ⟨first.val, firstSelector⟩ ∈
            (List.finRange p.selectorWidth).map selectorWire :=
        List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
      have scratchMember :
          sharedUniformScratchWire p
              ⟨second.val - p.selectorWidth, by omega⟩ ∈
            uniformScratchWires p :=
        sharedUniformScratchWire_mem_uniformScratchWires p _
      have crossEqual :
          selectorWire ⟨first.val, firstSelector⟩ =
            sharedUniformScratchWire p
              ⟨second.val - p.selectorWidth, by omega⟩ := by
        simpa [sharedUniformLocalWire, firstSelector, secondSelector] using equal
      exact (List.disjoint_left.mp selectorScratchDisjoint)
        selectorMember (crossEqual.symm ▸ scratchMember)
  · by_cases secondSelector : second.val < p.selectorWidth
    · exfalso
      have selectorMember :
          selectorWire ⟨second.val, secondSelector⟩ ∈
            (List.finRange p.selectorWidth).map selectorWire :=
        List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
      have scratchMember :
          sharedUniformScratchWire p
              ⟨first.val - p.selectorWidth, by omega⟩ ∈
            uniformScratchWires p :=
        sharedUniformScratchWire_mem_uniformScratchWires p _
      have crossEqual :
          selectorWire ⟨second.val, secondSelector⟩ =
            sharedUniformScratchWire p
              ⟨first.val - p.selectorWidth, by omega⟩ := by
        simpa [sharedUniformLocalWire, firstSelector, secondSelector] using equal.symm
      exact (List.disjoint_left.mp selectorScratchDisjoint)
        selectorMember (crossEqual.symm ▸ scratchMember)
    · have scratchEqual :
          sharedUniformScratchWire p
              ⟨first.val - p.selectorWidth, by omega⟩ =
            sharedUniformScratchWire p
              ⟨second.val - p.selectorWidth, by omega⟩ := by
        simpa [sharedUniformLocalWire, firstSelector, secondSelector] using equal
      have valueEqual : first.val - p.selectorWidth =
          second.val - p.selectorWidth := by
        have indexEqual :=
          (QLayout.oracleSlice
            (OracleWorkLayout.canonical p).andWork).ancillaWire_injective
            scratchEqual
        exact congrArg Fin.val indexEqual
      apply Fin.ext
      omega

/-- Q wire配置を共有coreの標準`Fin` wire配置へ持ち上げる。 -/
def sharedUniformCorePlacement
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    Fin (2 * p.selectorWidth) ↪ Fin (p.ancillaWidth + p.systemWidth) where
  toFun := wireToCanonicalFin ∘ sharedUniformLocalWire p selectorWire
  inj' := wireToCanonicalFin_injective.comp
    (sharedUniformLocalWire_injective p selectorWire selectorInjective
      selectorScratchDisjoint)

/-- Q背景基底から、配置外wireの固定値を共有core形式で読む。 -/
def sharedUniformOutsideBasis
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.OutsideWire
      (sharedUniformCorePlacement p selectorWire selectorInjective
        selectorScratchDisjoint) → Bool :=
  fun wire => jointBasisToCore background wire.1

/--
共有一様準備componentをQ selector/scratch配置と任意の固定背景基底へ持ち上げる。
戻り値は共有coreの標準基底上のcomponentであり、次段のcompiler bridgeが凍結Q ASTへ移す。
-/
def sharedUniformPreparationAtQLayout
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.StatePreparationComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) (fun _ => 0)) :=
  VerifiedCircuitCore.StatePreparationComponent.mapPrimitiveWiresAtFixedOutsideBasis
    (fun _ => 0)
    (sharedUniformCorePlacement p selectorWire selectorInjective
      selectorScratchDisjoint)
    (sharedUniformOutsideBasis p selectorWire selectorInjective
      selectorScratchDisjoint background)
    (VerifiedCircuitCore.zeroUniformPreparationBasis p.selectorWidth)
    (VerifiedCircuitCore.uniformPreparationStatePreparationComponent
      (sharedUniformPreparationParameters p))
    rfl

/-- Q配置へwire-liftした共有一様準備回路の全leafもcompiler可能である。 -/
theorem sharedUniformPreparationAtQLayout_leaf_compilable
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (gate : VerifiedCircuitCore.PrimitiveGate
      (p.ancillaWidth + p.systemWidth))
    (member : gate ∈
      (sharedUniformPreparationAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint background).circuit.flatten) :
    SharedUniformGateCompilable gate := by
  unfold sharedUniformPreparationAtQLayout at member
  change gate ∈
    ((VerifiedCircuitCore.uniformPreparationStatePreparationComponent
      (sharedUniformPreparationParameters p)).circuit.mapGates
        (VerifiedCircuitCore.PrimitiveGate.mapWires
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint))).flatten at member
  rw [VerifiedCircuitCore.Circuit.flatten_mapGates] at member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  apply primitiveGate_mapWires_sharedUniformGateCompilable
  exact uniformPreparationCircuit_sharedUniformCircuitCompilable
    (sharedUniformPreparationParameters p) source sourceMember

/--
共有一様準備componentをrestricted compilerでQ primitive ASTへ移した標準基底版。
compiler正しさは実際に現れるleafだけを公開membership定理から受け取る。
-/
def compiledSharedUniformPreparationOnCanonicalCore
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.StatePreparationComponent
      (qPrimitiveGateOperatorOnCanonicalCore
        (ancillaQubits := p.ancillaWidth)
        (systemQubits := p.systemWidth)) :=
  VerifiedCircuitCore.StatePreparationComponent.liftByCircuitCompiler
    (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
      (qubits := p.ancillaWidth + p.systemWidth) (fun _ => 0))
    qPrimitiveGateOperatorOnCanonicalCore
    compileSharedUniformCoreGate
    (MonoidHom.id
      (VerifiedCircuitCore.Operator
        (VerifiedCircuitCore.QubitBasis
          (p.ancillaWidth + p.systemWidth))))
    id
    (fun _ _ => rfl)
    (sharedUniformPreparationAtQLayout p selectorWire selectorInjective
      selectorScratchDisjoint background)
    (fun gate member => compileSharedUniformCoreGate_correct gate
      (sharedUniformPreparationAtQLayout_leaf_compilable p selectorWire
        selectorInjective selectorScratchDisjoint background gate member))

/-- restricted compiler結果を所属付きQ基底とQ primitive作用素へ戻す。 -/
def compiledSharedUniformPreparationOnJointBasis
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.StatePreparationComponent
      (primitiveGateOperator
        (ancillaQubits := p.ancillaWidth)
        (systemQubits := p.systemWidth)) :=
  VerifiedCircuitCore.StatePreparationComponent.liftByCompiler
    (qPrimitiveGateOperatorOnCanonicalCore
      (ancillaQubits := p.ancillaWidth)
      (systemQubits := p.systemWidth))
    primitiveGateOperator
    id
    (reindexCanonicalCoreOperatorToJoint
      (ancillaQubits := p.ancillaWidth)
      (systemQubits := p.systemWidth))
    reindexCanonicalCoreStateToJoint
    (fun gate => by
      change primitiveGateOperator gate =
        reindexCanonicalCoreOperatorToJoint
          (reindexJointOperatorToCanonicalCore
            (primitiveGateOperator gate))
      symm
      exact reindexCanonicalCoreOperatorToJoint_joint _)
    applyOperator_reindexCanonicalCoreToJoint
    (compiledSharedUniformPreparationOnCanonicalCore p selectorWire
      selectorInjective selectorScratchDisjoint background)

/--
局所core一様準備回路をQ配置へ写し、実際に現れる基本gateだけをQ primitive回路へ
展開するrestricted compiler。凍結ASTとの比較では、この回路の`flatten`を正規形にする。
-/
noncomputable def compileSharedUniformCircuitAtQLayout
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (circuit : VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate (2 * p.selectorWidth))) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  (circuit.mapGates
      (VerifiedCircuitCore.PrimitiveGate.mapWires
        (sharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint))).compileGates
    compileSharedUniformCoreGate

/-- restricted compilerは空回路を空回路へ移す。 -/
@[simp] theorem compileSharedUniformCircuitAtQLayout_identity
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint .identity = .identity := by
  rfl

/-- restricted compilerは二項逐次合成をそのまま保存する。 -/
@[simp] theorem compileSharedUniformCircuitAtQLayout_seq
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (first second : VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate (2 * p.selectorWidth))) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint (.seq first second) =
      .seq
        (compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
          selectorScratchDisjoint first)
        (compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
          selectorScratchDisjoint second) := by
  rfl

/-- 局所wireを配置してcanonical indexをQ wireへ戻すと、元のQ配置になる。 -/
@[simp] theorem canonicalFinToWire_sharedUniformCorePlacement
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (wire : Fin (2 * p.selectorWidth)) :
    canonicalFinToWire
        (sharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint wire) =
      sharedUniformLocalWire p selectorWire wire := by
  simp [sharedUniformCorePlacement]

/-- restricted compilerは配置済みcoreのX葉を同じQ wireのX葉へ移す。 -/
@[simp] theorem compileSharedUniformCircuitAtQLayout_gate_x
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (wire : Fin (2 * p.selectorWidth)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint (.gate (.x wire)) =
      .gate (.x (sharedUniformLocalWire p selectorWire wire)) := by
  simp [compileSharedUniformCircuitAtQLayout,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.compileGates,
    VerifiedCircuitCore.PrimitiveGate.mapWires,
    compileSharedUniformCoreGate]

/-- restricted compilerは配置済みcoreのRy葉を構造変換したQ角度のRy葉へ移す。 -/
@[simp] theorem compileSharedUniformCircuitAtQLayout_gate_ry
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (angle : VerifiedCircuitCore.AngleExpr)
    (wire : Fin (2 * p.selectorWidth)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint (.gate (.ry angle wire)) =
      .gate (.ry (sharedUniformLocalWire p selectorWire wire)
        (representableCoreAngleToQ angle)) := by
  simp [compileSharedUniformCircuitAtQLayout,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.compileGates,
    VerifiedCircuitCore.PrimitiveGate.mapWires,
    compileSharedUniformCoreGate]

/-- restricted compilerは配置済みcoreのCNOT葉を同じ二本のQ wireへ移す。 -/
@[simp] theorem compileSharedUniformCircuitAtQLayout_gate_cnot
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (control target : Fin (2 * p.selectorWidth))
    (different : control ≠ target) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint (.gate (.cnot control target different)) =
      .gate (.cnot (sharedUniformLocalWire p selectorWire control)
        (sharedUniformLocalWire p selectorWire target)
        ((sharedUniformLocalWire_injective p selectorWire selectorInjective
          selectorScratchDisjoint).ne different)) := by
  simp [compileSharedUniformCircuitAtQLayout,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.compileGates,
    VerifiedCircuitCore.PrimitiveGate.mapWires,
    compileSharedUniformCoreGate]

/-- restricted compilerは配置済みcoreのToffoli葉を同じ三本のQ wireへ移す。 -/
@[simp] theorem compileSharedUniformCircuitAtQLayout_gate_toffoli
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (first second target : Fin (2 * p.selectorWidth))
    (controlsDifferent : first ≠ second)
    (firstDifferent : first ≠ target)
    (secondDifferent : second ≠ target) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (.gate (.toffoli first second target controlsDifferent firstDifferent
          secondDifferent)) =
      .gate (.toffoli
        (sharedUniformLocalWire p selectorWire first)
        (sharedUniformLocalWire p selectorWire second)
        (sharedUniformLocalWire p selectorWire target)
        ((sharedUniformLocalWire_injective p selectorWire selectorInjective
          selectorScratchDisjoint).ne controlsDifferent)
        ((sharedUniformLocalWire_injective p selectorWire selectorInjective
          selectorScratchDisjoint).ne firstDifferent)
        ((sharedUniformLocalWire_injective p selectorWire selectorInjective
          selectorScratchDisjoint).ne secondDifferent)) := by
  simp [compileSharedUniformCircuitAtQLayout,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.compileGates,
    VerifiedCircuitCore.PrimitiveGate.mapWires,
    compileSharedUniformCoreGate]

/-- restricted compilerは型安全なcore CNOT constructorをQ側の同じconstructorへ移す。 -/
theorem compileSharedUniformCircuitAtQLayout_safeCnot
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (control target : Fin (2 * p.selectorWidth)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.safeCnot control target) =
      Circuit.safeCnot
        (sharedUniformLocalWire p selectorWire control)
        (sharedUniformLocalWire p selectorWire target) := by
  by_cases different : control ≠ target
  · have mappedDifferent :
        sharedUniformLocalWire p selectorWire control ≠
          sharedUniformLocalWire p selectorWire target :=
      (sharedUniformLocalWire_injective p selectorWire selectorInjective
        selectorScratchDisjoint).ne different
    simp [VerifiedCircuitCore.Circuit.safeCnot, Circuit.safeCnot,
      different, mappedDifferent]
  · have equal : control = target := not_ne_iff.mp different
    subst target
    have sourceSelf : ¬ (control ≠ control) := by simp
    have mappedSelf : ¬
        (sharedUniformLocalWire p selectorWire control ≠
          sharedUniformLocalWire p selectorWire control) := by simp
    simp only [VerifiedCircuitCore.Circuit.safeCnot, Circuit.safeCnot,
      dif_neg sourceSelf, dif_neg mappedSelf]
    rfl

/-- restricted compilerは型安全なcore Toffoli constructorをQ側の同じconstructorへ移す。 -/
theorem compileSharedUniformCircuitAtQLayout_safeToffoli
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (first second target : Fin (2 * p.selectorWidth)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.safeToffoli first second target) =
      Circuit.safeToffoli
        (sharedUniformLocalWire p selectorWire first)
        (sharedUniformLocalWire p selectorWire second)
        (sharedUniformLocalWire p selectorWire target) := by
  have injective := sharedUniformLocalWire_injective p selectorWire
    selectorInjective selectorScratchDisjoint
  unfold VerifiedCircuitCore.Circuit.safeToffoli Circuit.safeToffoli
  by_cases firstSecond : first ≠ second
  · have mappedFirstSecond := injective.ne firstSecond
    simp only [dif_pos firstSecond, dif_pos mappedFirstSecond]
    by_cases firstTarget : first ≠ target
    · have mappedFirstTarget := injective.ne firstTarget
      simp only [dif_pos firstTarget, dif_pos mappedFirstTarget]
      by_cases secondTarget : second ≠ target
      · have mappedSecondTarget := injective.ne secondTarget
        simp [secondTarget, mappedSecondTarget]
      · have equal : second = target := not_ne_iff.mp secondTarget
        subst target
        have sourceSelf : ¬ (second ≠ second) := by simp
        have mappedSelf : ¬
            (sharedUniformLocalWire p selectorWire second ≠
              sharedUniformLocalWire p selectorWire second) := by simp
        simp only [dif_neg sourceSelf, dif_neg mappedSelf]
        rfl
    · have equal : first = target := not_ne_iff.mp firstTarget
      subst target
      have sourceSelf : ¬ (first ≠ first) := by simp
      have mappedSelf : ¬
          (sharedUniformLocalWire p selectorWire first ≠
            sharedUniformLocalWire p selectorWire first) := by simp
      simp only [dif_neg sourceSelf, dif_neg mappedSelf]
      rfl
  · have equal : first = second := not_ne_iff.mp firstSecond
    subst second
    have sourceSelf : ¬ (first ≠ first) := by simp
    have mappedSelf : ¬
        (sharedUniformLocalWire p selectorWire first ≠
          sharedUniformLocalWire p selectorWire first) := by simp
    simp only [dif_neg sourceSelf, dif_neg mappedSelf]
    rfl

/-- restricted compilerはcoreの1-control Ry分解をQ側の同じ四gate分解へ移す。 -/
theorem compileSharedUniformCircuitAtQLayout_controlledRyMacroExpansion
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (control target : Fin (2 * p.selectorWidth))
    (different : control ≠ target)
    (angle : VerifiedCircuitCore.AngleExpr) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.controlledRyMacroExpansion control target
          different angle) =
      controlledRyCircuit
        (sharedUniformLocalWire p selectorWire control)
        (sharedUniformLocalWire p selectorWire target)
        ((sharedUniformLocalWire_injective p selectorWire selectorInjective
          selectorScratchDisjoint).ne different)
        (representableCoreAngleToQ angle) := by
  simp [VerifiedCircuitCore.Circuit.controlledRyMacroExpansion,
    controlledRyCircuit, compileSharedUniformCircuitAtQLayout,
    VerifiedCircuitCore.Circuit.fromList,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.compileGates,
    VerifiedCircuitCore.PrimitiveGate.mapWires,
    compileSharedUniformCoreGate,
    representableCoreAngleToQ,
    representableCoreAngleToQ_halfAngle]

/-- coreのAND-chain付きcontrolled RyをQ wire配置へ逐次合成の形を保って移す。 -/
theorem compileSharedUniformCircuitAtQLayout_andChainControlledRy
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (previous : Fin (2 * p.selectorWidth))
    (controls scratches : List (Fin (2 * p.selectorWidth)))
    (target : Fin (2 * p.selectorWidth))
    (angle : VerifiedCircuitCore.AngleExpr) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.andChainControlledRy previous controls
          scratches target angle) =
      Circuit.andChainControlledRy
        (sharedUniformLocalWire p selectorWire previous)
        (controls.map (sharedUniformLocalWire p selectorWire))
        (scratches.map (sharedUniformLocalWire p selectorWire))
        (sharedUniformLocalWire p selectorWire target)
        (representableCoreAngleToQ angle) := by
  induction controls generalizing previous scratches with
  | nil =>
      simp only [VerifiedCircuitCore.Circuit.andChainControlledRy,
        Circuit.andChainControlledRy, List.map_nil]
      by_cases different : previous ≠ target
      · have mappedDifferent :=
          (sharedUniformLocalWire_injective p selectorWire selectorInjective
            selectorScratchDisjoint).ne different
        simp only [dif_pos different, dif_pos mappedDifferent]
        exact
          compileSharedUniformCircuitAtQLayout_controlledRyMacroExpansion
            p selectorWire selectorInjective selectorScratchDisjoint
              previous target different angle
      · have equal : previous = target := not_ne_iff.mp different
        subst target
        have sourceSelf : ¬ (previous ≠ previous) := by simp
        have mappedSelf : ¬
            (sharedUniformLocalWire p selectorWire previous ≠
              sharedUniformLocalWire p selectorWire previous) := by simp
        simp only [dif_neg sourceSelf, dif_neg mappedSelf]
        exact compileSharedUniformCircuitAtQLayout_identity p selectorWire
          selectorInjective selectorScratchDisjoint
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil =>
          simp [VerifiedCircuitCore.Circuit.andChainControlledRy,
            Circuit.andChainControlledRy]
      | cons scratch scratches =>
          simp only [VerifiedCircuitCore.Circuit.andChainControlledRy,
            Circuit.andChainControlledRy, List.map_cons]
          rw [compileSharedUniformCircuitAtQLayout_seq,
            compileSharedUniformCircuitAtQLayout_safeToffoli,
            compileSharedUniformCircuitAtQLayout_seq,
            inductionHypothesis,
            compileSharedUniformCircuitAtQLayout_safeToffoli]

/-- coreの正制御multi-controlled Ry compilerをQ wire配置へそのまま移す。 -/
theorem compileSharedUniformCircuitAtQLayout_positiveMultiControlledRy
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (controls scratches : List (Fin (2 * p.selectorWidth)))
    (target : Fin (2 * p.selectorWidth))
    (angle : VerifiedCircuitCore.AngleExpr) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.positiveMultiControlledRy controls
          scratches target angle) =
      Circuit.positiveMultiControlledRy
        (controls.map (sharedUniformLocalWire p selectorWire))
        (scratches.map (sharedUniformLocalWire p selectorWire))
        (sharedUniformLocalWire p selectorWire target)
        (representableCoreAngleToQ angle) := by
  cases controls with
  | nil =>
      simp only [VerifiedCircuitCore.Circuit.positiveMultiControlledRy,
        Circuit.positiveMultiControlledRy, List.map_nil]
      exact compileSharedUniformCircuitAtQLayout_gate_ry p selectorWire
        selectorInjective selectorScratchDisjoint angle target
  | cons first controls =>
      cases controls with
      | nil =>
          simp only [VerifiedCircuitCore.Circuit.positiveMultiControlledRy,
            Circuit.positiveMultiControlledRy, List.map_cons, List.map_nil]
          by_cases different : first ≠ target
          · have mappedDifferent :=
              (sharedUniformLocalWire_injective p selectorWire
                selectorInjective selectorScratchDisjoint).ne different
            simp only [dif_pos different, dif_pos mappedDifferent]
            exact
              compileSharedUniformCircuitAtQLayout_controlledRyMacroExpansion
                p selectorWire selectorInjective selectorScratchDisjoint
                  first target different angle
          · have equal : first = target := not_ne_iff.mp different
            subst target
            have sourceSelf : ¬ (first ≠ first) := by simp
            have mappedSelf : ¬
                (sharedUniformLocalWire p selectorWire first ≠
                  sharedUniformLocalWire p selectorWire first) := by simp
            simp only [dif_neg sourceSelf, dif_neg mappedSelf]
            exact compileSharedUniformCircuitAtQLayout_identity p selectorWire
              selectorInjective selectorScratchDisjoint
      | cons second rest =>
          cases scratches with
          | nil =>
              simp [VerifiedCircuitCore.Circuit.positiveMultiControlledRy,
                Circuit.positiveMultiControlledRy]
          | cons scratch scratches =>
              simp only [VerifiedCircuitCore.Circuit.positiveMultiControlledRy,
                Circuit.positiveMultiControlledRy, List.map_cons]
              rw [compileSharedUniformCircuitAtQLayout_seq,
                compileSharedUniformCircuitAtQLayout_safeToffoli,
                compileSharedUniformCircuitAtQLayout_seq]
              cases rest with
              | nil =>
                  simp only [List.map_nil]
                  by_cases different : scratch ≠ target
                  · have mappedDifferent :=
                      (sharedUniformLocalWire_injective p selectorWire
                        selectorInjective selectorScratchDisjoint).ne different
                    simp only [dif_pos different, dif_pos mappedDifferent]
                    rw [compileSharedUniformCircuitAtQLayout_controlledRyMacroExpansion,
                      compileSharedUniformCircuitAtQLayout_safeToffoli]
                  · have equal : scratch = target := not_ne_iff.mp different
                    subst target
                    have sourceSelf : ¬ (scratch ≠ scratch) := by simp
                    have mappedSelf : ¬
                        (sharedUniformLocalWire p selectorWire scratch ≠
                          sharedUniformLocalWire p selectorWire scratch) := by simp
                    simp only [dif_neg sourceSelf, dif_neg mappedSelf]
                    rw [compileSharedUniformCircuitAtQLayout_identity,
                      compileSharedUniformCircuitAtQLayout_safeToffoli]
              | cons next rest =>
                  simp only [List.map_cons]
                  rw [compileSharedUniformCircuitAtQLayout_andChainControlledRy,
                    compileSharedUniformCircuitAtQLayout_safeToffoli]
                  simp only [List.map_cons]

/-- Xだけからなるcore gate列のrestricted compileは、wire写像後のQ X列である。 -/
theorem compileSharedUniformCircuitAtQLayout_fromList_x
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (wires : List (Fin (2 * p.selectorWidth))) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.fromList
          (wires.map VerifiedCircuitCore.PrimitiveGate.x)) =
      Circuit.fromList
        (wires.map fun wire =>
          PrimitiveGate.x (sharedUniformLocalWire p selectorWire wire)) := by
  induction wires with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp only [List.map_cons, VerifiedCircuitCore.Circuit.fromList]
      rw [compileSharedUniformCircuitAtQLayout_seq,
        compileSharedUniformCircuitAtQLayout_gate_x,
        inductionHypothesis]

/-- zero-control抽出後のwire列写像は、先にQ wireへ写してから抽出した列と一致する。 -/
theorem uniformZeroControlWires_map_sharedUniformLocalWire
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (controls : List (Fin (2 * p.selectorWidth) × Bool)) :
    (controls.filterMap fun control =>
        if control.2 then none else some control.1).map
          (sharedUniformLocalWire p selectorWire) =
      (controls.map fun control =>
        (sharedUniformLocalWire p selectorWire control.1,
          control.2)).filterMap fun control =>
            if control.2 then none else some control.1 := by
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨wire, expected⟩
      cases expected <;> simp [inductionHypothesis]

/-- zero-control用`filterMap`でwire写像をgate生成の外へ取り出す。 -/
theorem zeroControlGateFilterMap_eq_map
    {sourceWire targetGate : Type*}
    (makeGate : sourceWire → targetGate)
    (controls : List (sourceWire × Bool)) :
    controls.filterMap (fun control =>
        if control.2 then none else some (makeGate control.1)) =
      (controls.filterMap fun control =>
        if control.2 then none else some control.1).map makeGate := by
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨wire, expected⟩
      cases expected <;> simp [inductionHypothesis]

/-- zero-control反転列もcoreからQへwire順を保って移る。 -/
theorem compileSharedUniformCircuitAtQLayout_invertZeroControls
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (controls : List (Fin (2 * p.selectorWidth) × Bool)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.invertZeroControls controls) =
      Circuit.invertZeroControls
        (controls.map fun control =>
          (sharedUniformLocalWire p selectorWire control.1, control.2)) := by
  unfold VerifiedCircuitCore.Circuit.invertZeroControls
    Circuit.invertZeroControls
  rw [zeroControlGateFilterMap_eq_map
      VerifiedCircuitCore.PrimitiveGate.x controls]
  rw [zeroControlGateFilterMap_eq_map PrimitiveGate.x]
  rw [← uniformZeroControlWires_map_sharedUniformLocalWire p selectorWire]
  have gateListMap :
      ((controls.filterMap fun control =>
          if control.2 then none else some control.1).map
            (sharedUniformLocalWire p selectorWire)).map PrimitiveGate.x =
        (controls.filterMap fun control =>
          if control.2 then none else some control.1).map fun wire =>
            PrimitiveGate.x (sharedUniformLocalWire p selectorWire wire) := by
    rw [List.map_map]
    rfl
  rw [gateListMap]
  exact compileSharedUniformCircuitAtQLayout_fromList_x p selectorWire
    selectorInjective selectorScratchDisjoint _

/-- Bool制御multi-controlled Ry全体もcoreからQへ同じcompute-use-uncompute順で移る。 -/
theorem compileSharedUniformCircuitAtQLayout_boolMultiControlledRy
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (controls : List (Fin (2 * p.selectorWidth) × Bool))
    (scratches : List (Fin (2 * p.selectorWidth)))
    (target : Fin (2 * p.selectorWidth))
    (angle : VerifiedCircuitCore.AngleExpr) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.Circuit.boolMultiControlledRy controls scratches
          target angle) =
      Circuit.boolMultiControlledRy
        (controls.map fun control =>
          (sharedUniformLocalWire p selectorWire control.1, control.2))
        (scratches.map (sharedUniformLocalWire p selectorWire))
        (sharedUniformLocalWire p selectorWire target)
        (representableCoreAngleToQ angle) := by
  unfold VerifiedCircuitCore.Circuit.boolMultiControlledRy
    Circuit.boolMultiControlledRy
  rw [compileSharedUniformCircuitAtQLayout_seq,
    compileSharedUniformCircuitAtQLayout_invertZeroControls,
    compileSharedUniformCircuitAtQLayout_seq,
    compileSharedUniformCircuitAtQLayout_positiveMultiControlledRy,
    compileSharedUniformCircuitAtQLayout_invertZeroControls]
  have controlsMap :
      (controls.map Prod.fst).map (sharedUniformLocalWire p selectorWire) =
        (controls.map fun control =>
          (sharedUniformLocalWire p selectorWire control.1,
            control.2)).map Prod.fst := by
    induction controls with
    | nil => rfl
    | cons control controls inductionHypothesis =>
        simp [inductionHypothesis]
  rw [controlsMap]

/-- shared compilerが実際に使うAND work先頭`selectorWidth`本。 -/
def sharedUniformScratchPrefix (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map (sharedUniformScratchWire p)

/-- 局所selector wireのQ配置像は指定されたselector sliceそのものである。 -/
@[simp] theorem sharedUniformLocalWire_selector
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (wire : Fin p.selectorWidth) :
    sharedUniformLocalWire p selectorWire
        (VerifiedCircuitCore.uniformPreparationSelectorWire p.selectorWidth
          wire) =
      selectorWire wire := by
  simp [sharedUniformLocalWire,
    VerifiedCircuitCore.uniformPreparationSelectorWire]

/-- 局所scratch wireのQ配置像はAND work先頭の対応wireである。 -/
@[simp] theorem sharedUniformLocalWire_scratch
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (wire : Fin p.selectorWidth) :
    sharedUniformLocalWire p selectorWire
        (VerifiedCircuitCore.uniformPreparationScratchWire p.selectorWidth
          wire) =
      sharedUniformScratchWire p wire := by
  simp [sharedUniformLocalWire,
    VerifiedCircuitCore.uniformPreparationScratchWire]

/-- core局所scratch列をQへ配置すると、Q AND workの先頭prefixになる。 -/
theorem sharedUniformPreparationScratchWires_map
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth) :
    (VerifiedCircuitCore.uniformPreparationScratchWires p.selectorWidth).map
        (sharedUniformLocalWire p selectorWire) =
      sharedUniformScratchPrefix p := by
  simp [VerifiedCircuitCore.uniformPreparationScratchWires,
    sharedUniformScratchPrefix, List.map_map]

/-- core命令targetのQ配置像は、変換後Q命令のselector targetと一致する。 -/
theorem sharedUniformRotationInstructionTarget_eq
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (instruction : VerifiedCircuitCore.UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    sharedUniformLocalWire p selectorWire
        (VerifiedCircuitCore.uniformRotationInstructionTarget p.selectorWidth
          instruction wellFormed) =
      uniformInstructionTargetOn p selectorWire
        (coreUniformRotationInstructionToQ instruction)
        (coreUniformRotationInstructionToQ_wellFormed instruction
          wellFormed) := by
  simp [VerifiedCircuitCore.uniformRotationInstructionTarget,
    uniformInstructionTargetOn, coreUniformRotationInstructionToQ]

/-- core命令control列のQ配置像は、変換後Q命令のBool control列と一致する。 -/
theorem sharedUniformRotationInstructionControls_eq
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (instruction : VerifiedCircuitCore.UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    ((VerifiedCircuitCore.uniformRotationInstructionControls p.selectorWidth
        instruction wellFormed).map fun control =>
          (sharedUniformLocalWire p selectorWire control.1, control.2)) =
      uniformInstructionControlsOn p selectorWire
        (coreUniformRotationInstructionToQ instruction)
        (coreUniformRotationInstructionToQ_wellFormed instruction
          wellFormed) := by
  simp [VerifiedCircuitCore.uniformRotationInstructionControls,
    uniformInstructionControlsOn, coreUniformRotationInstructionToQ,
    List.map_map]

/-- 一命令のshared-core compileは、Q selectorとscratch prefix上の同じ命令回路になる。 -/
theorem compileSharedUniformRotationInstruction_eq_prefix
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (instruction : VerifiedCircuitCore.UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.compileUniformRotationInstruction p.selectorWidth
          instruction wellFormed) =
      Circuit.boolMultiControlledRy
        (uniformInstructionControlsOn p selectorWire
          (coreUniformRotationInstructionToQ instruction)
          (coreUniformRotationInstructionToQ_wellFormed instruction
            wellFormed))
        (sharedUniformScratchPrefix p)
        (uniformInstructionTargetOn p selectorWire
          (coreUniformRotationInstructionToQ instruction)
          (coreUniformRotationInstructionToQ_wellFormed instruction
            wellFormed))
        (coreUniformRotationInstructionToQ instruction).angle := by
  unfold VerifiedCircuitCore.compileUniformRotationInstruction
  rw [compileSharedUniformCircuitAtQLayout_boolMultiControlledRy]
  rw [sharedUniformRotationInstructionControls_eq,
    sharedUniformPreparationScratchWires_map,
    sharedUniformRotationInstructionTarget_eq]
  rfl

/-- AND-chainは必要本数を満たすscratch prefixより後ろのwireを読まない。 -/
theorem andChainControlledRy_append_unusedScratch
    {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits)
    (controls scratches extra : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (angle : AngleExpr)
    (enough : controls.length ≤ scratches.length) :
    Circuit.andChainControlledRy previous controls (scratches ++ extra)
        target angle =
      Circuit.andChainControlledRy previous controls scratches target angle := by
  induction controls generalizing previous scratches with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil => simp at enough
      | cons scratch scratches =>
          simp only [List.cons_append, Circuit.andChainControlledRy]
          rw [inductionHypothesis]
          simpa using enough

/-- 正制御multi-controlled Ryも必要本数より後ろのscratch suffixを読まない。 -/
theorem positiveMultiControlledRy_append_unusedScratch
    {ancillaQubits systemQubits : Nat}
    (controls scratches extra : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (angle : AngleExpr)
    (enough : controls.length ≤ scratches.length + 1) :
    Circuit.positiveMultiControlledRy controls (scratches ++ extra)
        target angle =
      Circuit.positiveMultiControlledRy controls scratches target angle := by
  cases controls with
  | nil => rfl
  | cons first controls =>
      cases controls with
      | nil => rfl
      | cons second rest =>
          cases scratches with
          | nil => simp at enough
          | cons scratch scratches =>
              simp only [List.cons_append,
                Circuit.positiveMultiControlledRy]
              cases rest with
              | nil => rfl
              | cons next rest =>
                  cases scratches with
                  | nil => simp at enough
                  | cons nextScratch scratches =>
                      rw [andChainControlledRy_append_unusedScratch]
                      simpa using enough

/-- Bool制御multi-controlled Ryも必要本数より後ろのscratch suffixを読まない。 -/
theorem boolMultiControlledRy_append_unusedScratch
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratches extra : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (angle : AngleExpr)
    (enough : controls.length ≤ scratches.length + 1) :
    Circuit.boolMultiControlledRy controls (scratches ++ extra) target angle =
      Circuit.boolMultiControlledRy controls scratches target angle := by
  unfold Circuit.boolMultiControlledRy
  rw [positiveMultiControlledRy_append_unusedScratch]
  simpa using enough

/-- Qの全uniform scratch列はshared prefixと未使用suffixへ分解できる。 -/
theorem uniformScratchWires_eq_sharedPrefix_append_drop (p : QParameters) :
    uniformScratchWires p =
      sharedUniformScratchPrefix p ++
        (uniformScratchWires p).drop p.selectorWidth := by
  have prefixTake :
      (uniformScratchWires p).take p.selectorWidth =
        sharedUniformScratchPrefix p := by
    apply List.ext_get
    · simp [uniformScratchWires, sharedUniformScratchPrefix,
        selectorWidth_le_andWorkWidth]
    · intro index leftBound rightBound
      simp [uniformScratchWires, sharedUniformScratchPrefix,
        sharedUniformScratchWire]
  calc
    uniformScratchWires p =
        (uniformScratchWires p).take p.selectorWidth ++
          (uniformScratchWires p).drop p.selectorWidth :=
      (List.take_append_drop p.selectorWidth (uniformScratchWires p)).symm
    _ = sharedUniformScratchPrefix p ++
          (uniformScratchWires p).drop p.selectorWidth := by rw [prefixTake]

/-- shared-core一命令のrestricted compileは、余剰scratchを含む凍結Q命令ASTに一致する。 -/
theorem compileSharedUniformRotationInstruction_eq_frozen
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (instruction : VerifiedCircuitCore.UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.compileUniformRotationInstruction p.selectorWidth
          instruction wellFormed) =
      compileUniformRotationInstructionOn p selectorWire
        (coreUniformRotationInstructionToQ instruction)
        (coreUniformRotationInstructionToQ_wellFormed instruction
          wellFormed) := by
  rw [compileSharedUniformRotationInstruction_eq_prefix]
  unfold compileUniformRotationInstructionOn
  have enough :
      (uniformInstructionControlsOn p selectorWire
        (coreUniformRotationInstructionToQ instruction)
        (coreUniformRotationInstructionToQ_wellFormed instruction
          wellFormed)).length ≤
        (sharedUniformScratchPrefix p).length + 1 := by
    rw [← sharedUniformRotationInstructionControls_eq p selectorWire
      instruction wellFormed]
    rw [← sharedUniformPreparationScratchWires_map p selectorWire]
    simpa using
      VerifiedCircuitCore.uniformRotationInstruction_enoughScratch
        p.selectorWidth instruction wellFormed
  rw [uniformScratchWires_eq_sharedPrefix_append_drop]
  symm
  exact boolMultiControlledRy_append_unusedScratch _ _ _ _ _ enough

/-- restricted compilerは有限回路列の`sequence`を子ごとのcompile列へ移す。 -/
theorem compileSharedUniformCircuitAtQLayout_sequence
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (circuits : List (VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate (2 * p.selectorWidth)))) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint (VerifiedCircuitCore.Circuit.sequence circuits) =
      Circuit.sequence
        (circuits.map fun circuit =>
          compileSharedUniformCircuitAtQLayout p selectorWire
            selectorInjective selectorScratchDisjoint circuit) := by
  induction circuits with
  | nil => rfl
  | cons circuit circuits inductionHypothesis =>
      simp only [VerifiedCircuitCore.Circuit.sequence, List.map_cons,
        compileSharedUniformCircuitAtQLayout_seq]
      rw [inductionHypothesis]

/--
shared-core一様準備回路をQへrestricted compileすると、同じselector配置上の凍結Q回路ASTに
厳密一致する。plan変換・命令変換・余剰scratch不使用だけを合成する。
-/
theorem compileSharedUniformPreparationCircuit_eq_frozenOnWires
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.uniformPreparationCircuit
          (sharedUniformPreparationParameters p)) =
      prepareUniformSelectorOnWiresCircuit p selectorWire := by
  unfold VerifiedCircuitCore.uniformPreparationCircuit
    prepareUniformSelectorOnWiresCircuit sharedUniformPreparationParameters
  rw [compileSharedUniformCircuitAtQLayout_sequence, List.map_map]
  congr 1
  calc
    (VerifiedCircuitCore.attachedUniformRotationPlan p.selectorWidth
        p.selectorCount p.selectorCount_le_capacity).map
        (fun instruction =>
          compileSharedUniformCircuitAtQLayout p selectorWire
            selectorInjective selectorScratchDisjoint
            (VerifiedCircuitCore.compileUniformRotationInstruction
              p.selectorWidth instruction.1 instruction.2)) =
      (VerifiedCircuitCore.attachedUniformRotationPlan p.selectorWidth
        p.selectorCount p.selectorCount_le_capacity).map
        (fun instruction =>
          compileUniformRotationInstructionOn p selectorWire
            (coreAttachedUniformRotationInstructionToQ instruction).1
            (coreAttachedUniformRotationInstructionToQ instruction).2) := by
        apply List.map_congr_left
        intro instruction _
        exact compileSharedUniformRotationInstruction_eq_frozen p selectorWire
          selectorInjective selectorScratchDisjoint instruction.1 instruction.2
    _ = ((VerifiedCircuitCore.attachedUniformRotationPlan p.selectorWidth
        p.selectorCount p.selectorCount_le_capacity).map
          coreAttachedUniformRotationInstructionToQ).map
        (fun instruction =>
          compileUniformRotationInstructionOn p selectorWire
            instruction.1 instruction.2) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro instruction _
      rfl
    _ = (attachedUniformRotationPlan p.selectorWidth p.selectorCount
        p.selectorCount_le_capacity).map
        (fun instruction =>
          compileUniformRotationInstructionOn p selectorWire
            instruction.1 instruction.2) := by
      rw [coreAttachedUniformRotationPlan_map_toQ]

/-- JointBasisへ戻したshared componentのgate列は凍結Q一様準備gate列と完全一致する。 -/
theorem compiledSharedUniformPreparationOnJointBasis_flatten_eq_frozenOnWires
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (compiledSharedUniformPreparationOnJointBasis p selectorWire
        selectorInjective selectorScratchDisjoint background).circuit.flatten =
      (prepareUniformSelectorOnWiresCircuit p selectorWire).flatten := by
  change
    ((compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
      selectorScratchDisjoint
      (VerifiedCircuitCore.uniformPreparationCircuit
        (sharedUniformPreparationParameters p))).mapGates id).flatten = _
  rw [VerifiedCircuitCore.Circuit.flatten_mapGates]
  simp only [List.map_id_fun]
  rw [compileSharedUniformPreparationCircuit_eq_frozenOnWires]
  rfl

/-- JointBasisへ戻したshared componentの回路AST自体が凍結Q一様準備回路に一致する。 -/
theorem compiledSharedUniformPreparationOnJointBasis_circuit_eq_frozenOnWires
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (compiledSharedUniformPreparationOnJointBasis p selectorWire
        selectorInjective selectorScratchDisjoint background).circuit =
      prepareUniformSelectorOnWiresCircuit p selectorWire := by
  change
    (compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
      selectorScratchDisjoint
      (VerifiedCircuitCore.uniformPreparationCircuit
        (sharedUniformPreparationParameters p))).mapGates id = _
  rw [VerifiedCircuitCore.Circuit.mapGates_id]
  exact compileSharedUniformPreparationCircuit_eq_frozenOnWires p selectorWire
    selectorInjective selectorScratchDisjoint

/-- component回路と凍結Q回路は全空間の理想作用素としても一致する。 -/
theorem compiledSharedUniformPreparationOnJointBasis_denote_eq_frozenOnWires
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (compiledSharedUniformPreparationOnJointBasis p selectorWire
        selectorInjective selectorScratchDisjoint background).circuit.denote
          primitiveGateOperator =
      (prepareUniformSelectorOnWiresCircuit p selectorWire).denote
        primitiveGateOperator := by
  rw [compiledSharedUniformPreparationOnJointBasis_circuit_eq_frozenOnWires]

/-- 凍結Q ASTを回路fieldに持ち、shared coreの状態準備契約をそのまま再利用するcomponent。 -/
def frozenUniformPreparationOnJointBasisComponent
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.StatePreparationComponent
      (primitiveGateOperator
        (ancillaQubits := p.ancillaWidth)
        (systemQubits := p.systemWidth)) := by
  let shared := compiledSharedUniformPreparationOnJointBasis p selectorWire
    selectorInjective selectorScratchDisjoint background
  exact
    { circuit := prepareUniformSelectorOnWiresCircuit p selectorWire
      initialState := shared.initialState
      targetState := shared.targetState
      correct := by
        rw [← compiledSharedUniformPreparationOnJointBasis_circuit_eq_frozenOnWires
          p selectorWire selectorInjective selectorScratchDisjoint background]
        exact shared.correct }

/-- column selector局所indexからQ wireへの写像は単射である。 -/
theorem sharedColumnSelectorWire_injective (p : QParameters) :
    Function.Injective (columnSelectorWire p) :=
  (QLayout.canonical p).columnSelector.ancillaWire_injective

/-- row selector局所indexからQ wireへの写像は単射である。 -/
theorem sharedRowSelectorWire_injective (p : QParameters) :
    Function.Injective (rowSelectorWire p) :=
  (QLayout.canonical p).rowSelector.ancillaWire_injective

/-- column selector sliceとshared一様準備scratchは互いに素である。 -/
theorem sharedColumnSelector_uniformScratch_disjoint (p : QParameters) :
    ((List.finRange p.selectorWidth).map (columnSelectorWire p)).Disjoint
      (uniformScratchWires p) := by
  change (((QLayout.canonical p).columnSelector.wireList :
      List (Wire p.ancillaWidth p.systemWidth))).Disjoint
    ((QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).wireList)
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical, QLayout.oracleSlice, OracleWorkLayout.canonical,
    RegisterSlice.compose, QParameters.oracleWorkWidth]
  omega

/-- row selector sliceとshared一様準備scratchは互いに素である。 -/
theorem sharedRowSelector_uniformScratch_disjoint (p : QParameters) :
    ((List.finRange p.selectorWidth).map (rowSelectorWire p)).Disjoint
      (uniformScratchWires p) := by
  change (((QLayout.canonical p).rowSelector.wireList :
      List (Wire p.ancillaWidth p.systemWidth))).Disjoint
    ((QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).wireList)
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical, QLayout.oracleSlice, OracleWorkLayout.canonical,
    RegisterSlice.compose, QParameters.oracleWorkWidth]
  omega

/-- 凍結column一様準備AST上のshared-core状態準備component。 -/
def sharedColumnUniformPreparationOnJointBasisComponent
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.StatePreparationComponent
      (primitiveGateOperator
        (ancillaQubits := p.ancillaWidth)
        (systemQubits := p.systemWidth)) :=
  frozenUniformPreparationOnJointBasisComponent p (columnSelectorWire p)
    (sharedColumnSelectorWire_injective p)
    (sharedColumnSelector_uniformScratch_disjoint p) background

/-- 凍結row一様準備AST上のshared-core状態準備component。 -/
def sharedRowUniformPreparationOnJointBasisComponent
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.StatePreparationComponent
      (primitiveGateOperator
        (ancillaQubits := p.ancillaWidth)
        (systemQubits := p.systemWidth)) :=
  frozenUniformPreparationOnJointBasisComponent p (rowSelectorWire p)
    (sharedRowSelectorWire_injective p)
    (sharedRowSelector_uniformScratch_disjoint p) background

/-- shared column componentの回路fieldは凍結column一様準備回路そのものである。 -/
@[simp] theorem sharedColumnUniformPreparationOnJointBasisComponent_circuit
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (sharedColumnUniformPreparationOnJointBasisComponent p background).circuit =
      prepareUniformColumnSelectorCircuit p := by
  rfl

/-- shared row componentの回路fieldは凍結row一様準備回路そのものである。 -/
@[simp] theorem sharedRowUniformPreparationOnJointBasisComponent_circuit
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (sharedRowUniformPreparationOnJointBasisComponent p background).circuit =
      prepareUniformRowSelectorCircuit p := by
  rfl

end

end ProbabilityGeneratorQProof

namespace ProbabilityGeneratorQProof

noncomputable section

section NormalizedMacro

theorem controlledRyMacroCircuit_sharedUniformCircuitCompilable
    {qubits : Nat} (spec : VerifiedCircuitCore.ControlledRySpec qubits)
    (represented : CoreAngleRepresentable spec.angle) :
    SharedUniformCircuitCompilable
      (VerifiedCircuitCore.controlledRyMacroCircuit spec) := by
  simpa [VerifiedCircuitCore.controlledRyMacroCircuit] using
    (controlledRyMacroExpansion_sharedUniformCircuitCompilable
      spec.control spec.target spec.different spec.angle represented)

theorem compileSharedUniformCircuitAtQLayout_controlledRyMacroCircuit
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (spec : VerifiedCircuitCore.ControlledRySpec (2 * p.selectorWidth)) :
    compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint
        (VerifiedCircuitCore.controlledRyMacroCircuit spec) =
      controlledRyCircuit
        (sharedUniformLocalWire p selectorWire spec.control)
        (sharedUniformLocalWire p selectorWire spec.target)
        ((sharedUniformLocalWire_injective p selectorWire selectorInjective
          selectorScratchDisjoint).ne spec.different)
        (representableCoreAngleToQ spec.angle) := by
  simpa [VerifiedCircuitCore.controlledRyMacroCircuit] using
    (compileSharedUniformCircuitAtQLayout_controlledRyMacroExpansion
      p selectorWire selectorInjective selectorScratchDisjoint
      spec.control spec.target spec.different spec.angle)

theorem controlledRyMacroCircuit_source_order
    {qubits : Nat} (spec : VerifiedCircuitCore.ControlledRySpec qubits) :
    VerifiedCircuitCore.controlledRyMacroCircuit spec =
      VerifiedCircuitCore.Circuit.controlledRyMacroExpansion
        spec.control spec.target spec.different spec.angle := rfl

end NormalizedMacro

end

end ProbabilityGeneratorQProof

namespace ProbabilityGeneratorQProof

open VerifiedCircuitCore

noncomputable section

section NormalizedMacroEstablishedBridge

theorem controlledRyMacroCircuit_sharedUniform_control_target_different
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (spec : VerifiedCircuitCore.ControlledRySpec (2 * p.selectorWidth)) :
    sharedUniformLocalWire p selectorWire spec.control ≠
      sharedUniformLocalWire p selectorWire spec.target := by
  exact (sharedUniformLocalWire_injective p selectorWire selectorInjective
    selectorScratchDisjoint).ne spec.different

end NormalizedMacroEstablishedBridge

end

end ProbabilityGeneratorQProof
