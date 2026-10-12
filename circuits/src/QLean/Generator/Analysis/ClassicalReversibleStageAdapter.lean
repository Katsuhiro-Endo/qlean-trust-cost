import QLean.Generator.Analysis.TotalReversibleStage
import QLean.Generator.Analysis.SharedUniformPreparationFullOperator
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic

/-!
# 共有 classical reversible stage と Q wire stage の純粋な対応

共有 core は数値 wire `Fin (ancilla + system)` を用い、Q 証明は所属付き `Wire` を
用いる。この module は両者の純粋な構文変換だけを定義する。回路 compiler や回路意味論は
参照しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 所属付き Q wire と共有 core の標準数値 wire の同値。 -/
def analyticCanonicalWireEquiv (ancillaQubits systemQubits : Nat) :
    Wire ancillaQubits systemQubits ≃ Fin (ancillaQubits + systemQubits) where
  toFun := analyticWireToCanonicalFin
  invFun := analyticCanonicalFinToWire
  left_inv := analyticCanonicalFinToWire_wireToCanonicalFin
  right_inv := analyticWireToCanonicalFin_canonicalFinToWire

/-- 標準数値化後のwire等式は元の所属付きwire等式と同値である。 -/
@[simp] theorem analyticWireToCanonicalFin_eq_iff
    {ancillaQubits systemQubits : Nat}
    (left right : Wire ancillaQubits systemQubits) :
    analyticWireToCanonicalFin left = analyticWireToCanonicalFin right ↔
      left = right :=
  (analyticCanonicalWireEquiv ancillaQubits systemQubits).apply_eq_iff_eq

/-- Q wire列を共有coreの数値wire列へ写す。 -/
def analyticWiresToCore {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits)) :
    List (Fin (ancillaQubits + systemQubits)) :=
  wires.map (analyticCanonicalWireEquiv ancillaQubits systemQubits)

/-- Bool値付きQ control列を共有coreへ写す。 -/
def analyticControlsToCore {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    List (Fin (ancillaQubits + systemQubits) × Bool) :=
  controls.map fun control =>
    (analyticCanonicalWireEquiv ancillaQubits systemQubits control.1, control.2)

/-- 共有coreの数値wire列をQ wire列へ戻す。 -/
def analyticWiresOfCore {ancillaQubits systemQubits : Nat}
    (wires : List (Fin (ancillaQubits + systemQubits))) :
    List (Wire ancillaQubits systemQubits) :=
  wires.map (analyticCanonicalWireEquiv ancillaQubits systemQubits).symm

/-- Q wire列の共有core往復は恒等である。 -/
@[simp] theorem analyticWiresOfCore_toCore
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits)) :
    analyticWiresOfCore (analyticWiresToCore wires) = wires := by
  simp [analyticWiresOfCore, analyticWiresToCore]

/-- 共有core wire列のQ往復も恒等である。 -/
@[simp] theorem analyticWiresToCore_ofCore
    {ancillaQubits systemQubits : Nat}
    (wires : List (Fin (ancillaQubits + systemQubits))) :
    analyticWiresToCore (analyticWiresOfCore wires) = wires := by
  simp [analyticWiresOfCore, analyticWiresToCore]

/-- 0-control抽出はQ wireと共有core wireの標準同値を保つ。 -/
theorem analyticWiresOfCore_zeroControlWires
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    analyticWiresOfCore
        (VerifiedCircuitCore.ClassicalReversibleStage.zeroControlWires
          (analyticControlsToCore controls)) =
      controls.filterMap fun control =>
        if control.2 then none else some control.1 := by
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨wire, value⟩
      cases value with
      | false =>
          change
            (analyticCanonicalWireEquiv ancillaQubits systemQubits).symm
                (analyticCanonicalWireEquiv ancillaQubits systemQubits wire) ::
              analyticWiresOfCore
                (VerifiedCircuitCore.ClassicalReversibleStage.zeroControlWires
                  (analyticControlsToCore controls)) =
            wire :: controls.filterMap (fun control =>
              if control.2 then none else some control.1)
          simp [inductionHypothesis]
      | true =>
          change
            analyticWiresOfCore
                (VerifiedCircuitCore.ClassicalReversibleStage.zeroControlWires
                  (analyticControlsToCore controls)) =
              controls.filterMap (fun control =>
                if control.2 then none else some control.1)
          exact inductionHypothesis

/-- Bool control列のfirst projectionは標準wire写像と可換である。 -/
theorem analyticControlsToCore_map_fst
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    (analyticControlsToCore controls).map Prod.fst =
      analyticWiresToCore (controls.map Prod.fst) := by
  simp [analyticControlsToCore, analyticWiresToCore, List.map_map,
    Function.comp_def]

/-- 三本のQ wire列のzipは、標準wire写像を各entryへ作用させることと可換である。 -/
theorem analyticWiresToCore_zip3
    {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits)) :
    (analyticWiresToCore left).zip
        ((analyticWiresToCore right).zip (analyticWiresToCore flags)) =
      (left.zip (right.zip flags)).map fun entry =>
        (analyticCanonicalWireEquiv ancillaQubits systemQubits entry.1,
          (analyticCanonicalWireEquiv ancillaQubits systemQubits entry.2.1,
            analyticCanonicalWireEquiv ancillaQubits systemQubits entry.2.2)) := by
  induction left generalizing right flags with
  | nil => rfl
  | cons left lefts inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons right rights =>
          cases flags with
          | nil => rfl
          | cons flag flags =>
              simp only [analyticWiresToCore, List.map_cons, List.zip_cons_cons]
              congr 1
              simpa only [analyticWiresToCore] using
                inductionHypothesis rights flags

namespace TotalReversibleInstruction

/-- Q 所属付きwire命令を共有 core の数値wire命令へ写す。 -/
def toCore {ancillaQubits systemQubits : Nat} :
    TotalReversibleInstruction ancillaQubits systemQubits →
      VerifiedCircuitCore.ClassicalReversibleInstruction
        (ancillaQubits + systemQubits)
  | .xorOne target =>
      .xorOne (analyticCanonicalWireEquiv ancillaQubits systemQubits target)
  | .xorControlled control target different =>
      .xorControlled
        (analyticCanonicalWireEquiv ancillaQubits systemQubits control)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target)
        (fun equal => different
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
  | .xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      .xorDoublyControlled
        (analyticCanonicalWireEquiv ancillaQubits systemQubits control₁)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits control₂)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target)
        (fun equal => controlsDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
        (fun equal => firstDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
        (fun equal => secondDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))

/-- A Q instruction and its shared-core image have conjugate pure basis actions. -/
theorem toCore_basisAction_apply {ancillaQubits systemQubits : Nat}
    (instruction : TotalReversibleInstruction ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    instruction.toCore.basisAction
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) =
      analyticJointBasisCoreEquiv ancillaQubits systemQubits
        (instruction.reference input) := by
  cases instruction with
  | xorOne target =>
      funext index
      have indexTarget :
          index = analyticWireToCanonicalFin target ↔
            analyticCanonicalFinToWire index = target := by
        constructor
        · intro equal
          subst index
          simp
        · intro equal
          rw [← equal]
          simp
      by_cases atTarget : analyticCanonicalFinToWire index = target <;>
        simp [toCore, VerifiedCircuitCore.ClassicalReversibleInstruction.basisAction,
          reference, xBasisEquiv, xBasisAction, VerifiedCircuitCore.xorWire,
          analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv,
          Function.update_apply, indexTarget, atTarget]
  | xorControlled control target different =>
      funext index
      have indexTarget :
          index = analyticWireToCanonicalFin target ↔
            analyticCanonicalFinToWire index = target := by
        constructor
        · intro equal
          subst index
          simp
        · intro equal
          rw [← equal]
          simp
      cases controlValue : input control <;>
        by_cases atTarget : analyticCanonicalFinToWire index = target <;>
        simp [toCore, VerifiedCircuitCore.ClassicalReversibleInstruction.basisAction,
          reference, cnotBasisEquiv, cnotBasisAction,
          VerifiedCircuitCore.xorWire, analyticJointBasisCoreEquiv,
          analyticCanonicalWireEquiv, Function.update_apply, indexTarget,
          controlValue, atTarget]
  | xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      funext index
      have indexTarget :
          index = analyticWireToCanonicalFin target ↔
            analyticCanonicalFinToWire index = target := by
        constructor
        · intro equal
          subst index
          simp
        · intro equal
          rw [← equal]
          simp
      cases firstValue : input control₁ <;>
        cases secondValue : input control₂ <;>
        by_cases atTarget : analyticCanonicalFinToWire index = target <;>
        simp [toCore, VerifiedCircuitCore.ClassicalReversibleInstruction.basisAction,
          reference, toffoliBasisEquiv, toffoliBasisAction,
          VerifiedCircuitCore.xorWire, analyticJointBasisCoreEquiv,
          analyticCanonicalWireEquiv, Function.update_apply, indexTarget,
          firstValue, secondValue, atTarget]

/-- 共有 core の数値wire命令を Q 所属付きwire命令へ戻す。 -/
def ofCore {ancillaQubits systemQubits : Nat} :
    VerifiedCircuitCore.ClassicalReversibleInstruction
        (ancillaQubits + systemQubits) →
      TotalReversibleInstruction ancillaQubits systemQubits
  | .xorOne target =>
      .xorOne ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm target)
  | .xorControlled control target different =>
      .xorControlled
        ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm control)
        ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm target)
        (fun equal => different
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm.injective equal))
  | .xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      .xorDoublyControlled
        ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm control₁)
        ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm control₂)
        ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm target)
        (fun equal => controlsDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm.injective equal))
        (fun equal => firstDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm.injective equal))
        (fun equal => secondDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm.injective equal))

/-- Q命令を共有coreへ写して戻すと元の命令になる。 -/
@[simp] theorem ofCore_toCore {ancillaQubits systemQubits : Nat}
    (instruction : TotalReversibleInstruction ancillaQubits systemQubits) :
    ofCore (toCore instruction) = instruction := by
  cases instruction <;>
    simp [toCore, ofCore, analyticCanonicalWireEquiv]

/-- 共有core命令をQへ戻して再符号化すると元の命令になる。 -/
@[simp] theorem toCore_ofCore {ancillaQubits systemQubits : Nat}
    (instruction : VerifiedCircuitCore.ClassicalReversibleInstruction
      (ancillaQubits + systemQubits)) :
    toCore (ofCore (ancillaQubits := ancillaQubits)
      (systemQubits := systemQubits) instruction) = instruction := by
  cases instruction <;>
    simp [toCore, ofCore, analyticCanonicalWireEquiv]

end TotalReversibleInstruction

/-- Reindexing a Q X action is the shared single-wire XOR action. -/
theorem analyticJointBasisCoreEquiv_xBasisAction
    {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    analyticJointBasisCoreEquiv ancillaQubits systemQubits
        (xBasisAction wire input) =
      VerifiedCircuitCore.xorWire
        (analyticCanonicalWireEquiv ancillaQubits systemQubits wire) true
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) := by
  symm
  simpa [TotalReversibleInstruction.toCore,
    VerifiedCircuitCore.ClassicalReversibleInstruction.basisAction,
    TotalReversibleInstruction.reference, xBasisEquiv] using
    (TotalReversibleInstruction.toCore_basisAction_apply
      (TotalReversibleInstruction.xorOne wire) input)

namespace TotalReversibleStage

/-- Q stageを共有 core stageへ構造的に写す。 -/
def toCore {ancillaQubits systemQubits : Nat} :
    TotalReversibleStage ancillaQubits systemQubits →
      VerifiedCircuitCore.ClassicalReversibleStage
        (ancillaQubits + systemQubits)
  | .identity => .identity
  | .instruction value => .instruction value.toCore
  | .seq first second => .seq first.toCore second.toCore
  | .repeat count body => .repeat count body.toCore

/-- A Q stage and its shared-core image have conjugate pure references. -/
theorem toCore_reference_apply {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    stage.toCore.reference
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) =
      analyticJointBasisCoreEquiv ancillaQubits systemQubits
        (stage.reference input) := by
  induction stage generalizing input with
  | identity => rfl
  | instruction value =>
      exact TotalReversibleInstruction.toCore_basisAction_apply value input
  | seq first second firstInduction secondInduction =>
      change second.toCore.reference
          (first.toCore.reference
            (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)) =
        analyticJointBasisCoreEquiv ancillaQubits systemQubits
          (second.reference (first.reference input))
      rw [firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      change (body.toCore.reference ^ count)
          (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) =
        analyticJointBasisCoreEquiv ancillaQubits systemQubits
          ((body.reference ^ count) input)
      induction count generalizing input with
      | zero => rfl
      | succ count countInduction =>
          rw [pow_succ, pow_succ]
          change (body.toCore.reference ^ count)
              (body.toCore.reference
                (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)) =
            analyticJointBasisCoreEquiv ancillaQubits systemQubits
              ((body.reference ^ count) (body.reference input))
          rw [inductionHypothesis]
          exact countInduction (body.reference input)

/-- The Q-to-core stage adapter preserves finite execution-order sequences. -/
theorem toCore_sequence {ancillaQubits systemQubits : Nat}
    (stages : List (TotalReversibleStage ancillaQubits systemQubits)) :
    (TotalReversibleStage.sequence stages).toCore =
      VerifiedCircuitCore.ClassicalReversibleStage.sequence
        (stages.map TotalReversibleStage.toCore) := by
  induction stages with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [TotalReversibleStage.sequence,
        VerifiedCircuitCore.ClassicalReversibleStage.sequence, toCore,
        inductionHypothesis]

/-- Reindexing a Q stage's independent operator gives the independent operator
of its shared-core image. -/
theorem reindex_analyticOperator_eq_toCore {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    Matrix.reindex (analyticJointBasisCoreEquiv ancillaQubits systemQubits)
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits)
        stage.analyticOperator =
      stage.toCore.analyticOperator := by
  rw [stage.analyticOperator_eq_deterministicReference,
    stage.toCore.analyticOperator_eq_deterministicReference]
  ext output input
  simp only [Matrix.reindex_apply, VerifiedCircuitCore.deterministicOperator_apply]
  rw [show stage.toCore.reference input =
      analyticJointBasisCoreEquiv ancillaQubits systemQubits
        (stage.reference
          ((analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm input)) by
      simpa using stage.toCore_reference_apply
        ((analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm input)]
  change
    (if (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm output =
        stage.reference
          ((analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm input)
      then 1 else 0) =
      (if output = analyticJointBasisCoreEquiv ancillaQubits systemQubits
          (stage.reference
            ((analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm input))
        then 1 else 0)
  by_cases equal :
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm output =
        stage.reference
          ((analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm input)
  · rw [if_pos equal, if_pos]
    have mapped := congrArg
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits) equal
    simpa using mapped
  · rw [if_neg equal, if_neg]
    intro mappedEqual
    apply equal
    have mapped := congrArg
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm mappedEqual
    simpa using mapped

/-- 共有 core stageをQ stageへ構造的に戻す。 -/
def ofCore {ancillaQubits systemQubits : Nat} :
    VerifiedCircuitCore.ClassicalReversibleStage
        (ancillaQubits + systemQubits) →
      TotalReversibleStage ancillaQubits systemQubits
  | .identity => .identity
  | .instruction value =>
      .instruction (TotalReversibleInstruction.ofCore value)
  | .seq first second => .seq (ofCore first) (ofCore second)
  | .repeat count body => .repeat count (ofCore body)

/-- Q stageの共有core往復は恒等である。 -/
@[simp] theorem ofCore_toCore {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    ofCore (toCore stage) = stage := by
  induction stage with
  | identity => rfl
  | instruction value =>
      simp [toCore, ofCore, TotalReversibleInstruction.ofCore_toCore]
  | seq first second firstInduction secondInduction =>
      simp [toCore, ofCore, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp [toCore, ofCore, inductionHypothesis]

/-- 共有core stageのQ往復も恒等である。 -/
@[simp] theorem toCore_ofCore {ancillaQubits systemQubits : Nat}
    (stage : VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits)) :
    toCore (ofCore (ancillaQubits := ancillaQubits)
      (systemQubits := systemQubits) stage) = stage := by
  induction stage with
  | identity => rfl
  | instruction value =>
      simp [toCore, ofCore, TotalReversibleInstruction.toCore_ofCore]
  | seq first second firstInduction secondInduction =>
      simp [toCore, ofCore, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp [toCore, ofCore, inductionHypothesis]

end TotalReversibleStage

end

end ProbabilityGeneratorQProof
