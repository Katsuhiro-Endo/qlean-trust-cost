import QLean.Generator.Analysis.TotalReversiblePrograms
import QLean.Generator.Implementation.TotalReversibleStageCompiler
import QLean.Generator.Implementation.ReversibleArithmetic

/-!
# 可逆局所programのcompiler一致

純粋stage compilerが既存の作用中心回路constructorと同じASTを返すことを証明する。
-/

namespace ProbabilityGeneratorQProof

namespace TotalReversibleStage

/-- safe controlled XORのcompilerは既存safe CNOT constructorと一致する。 -/
theorem compile_safeXorControlled {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits) :
    (safeXorControlled control target).compile =
      ReversibleCircuit.safeCnot control target := by
  by_cases different : control ≠ target
  · simp [safeXorControlled,
      VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled,
      TotalReversibleStage.ofCore, TotalReversibleInstruction.ofCore,
      analyticCanonicalWireEquiv, ReversibleCircuit.safeCnot, different,
      TotalReversibleInstruction.toReversibleGate, TotalReversibleStage.compile]
  · simp [safeXorControlled,
      VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled,
      TotalReversibleStage.ofCore, analyticCanonicalWireEquiv,
      ReversibleCircuit.safeCnot, different, TotalReversibleStage.compile]

/-- safe doubly-controlled XORのcompilerは既存safe Toffoli constructorと一致する。 -/
theorem compile_safeXorDoublyControlled {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits) :
    (safeXorDoublyControlled control₁ control₂ target).compile =
      ReversibleCircuit.safeToffoli control₁ control₂ target := by
  by_cases controlsDifferent : control₁ ≠ control₂
  · by_cases firstDifferent : control₁ ≠ target
    · by_cases secondDifferent : control₂ ≠ target
      · simp [safeXorDoublyControlled, ReversibleCircuit.safeToffoli,
          VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled,
          TotalReversibleStage.ofCore, TotalReversibleInstruction.ofCore,
          analyticCanonicalWireEquiv,
          controlsDifferent, firstDifferent, secondDifferent,
          TotalReversibleStage.compile,
          TotalReversibleInstruction.toReversibleGate]
      · simp [safeXorDoublyControlled, ReversibleCircuit.safeToffoli,
          VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled,
          TotalReversibleStage.ofCore, analyticCanonicalWireEquiv,
          controlsDifferent, firstDifferent, secondDifferent,
          TotalReversibleStage.compile]
    · simp [safeXorDoublyControlled, ReversibleCircuit.safeToffoli,
        VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled,
        TotalReversibleStage.ofCore, analyticCanonicalWireEquiv,
        controlsDifferent, firstDifferent, TotalReversibleStage.compile]
  · simp [safeXorDoublyControlled, ReversibleCircuit.safeToffoli,
      VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled,
      TotalReversibleStage.ofCore, analyticCanonicalWireEquiv,
      controlsDifferent, TotalReversibleStage.compile]

/-- 共有coreのsafe controlled XORをQ wireへ移すcompiler bridge。 -/
theorem compileCoreStageToReversibleGate_safeXorControlled
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled
          (analyticCanonicalWireEquiv ancillaQubits systemQubits control)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
      ReversibleCircuit.safeCnot control target := by
  rw [← compile_ofCore]
  exact compile_safeXorControlled control target

/-- 共有coreのsafe doubly-controlled XORをQ wireへ移すcompiler bridge。 -/
theorem compileCoreStageToReversibleGate_safeXorDoublyControlled
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled
          (analyticCanonicalWireEquiv ancillaQubits systemQubits control₁)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits control₂)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
      ReversibleCircuit.safeToffoli control₁ control₂ target := by
  rw [← compile_ofCore]
  exact compile_safeXorDoublyControlled control₁ control₂ target

/-- 共有coreのuncontrolled XOR葉をQ wireへ移すcompiler bridge。 -/
@[simp] theorem compileCoreStageToReversibleGate_xorOne
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (.instruction (.xorOne
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target))) =
      .gate (.x target) := by
  change VerifiedCircuitCore.Circuit.gate (coreInstructionToReversibleGate
    (.xorOne (analyticCanonicalWireEquiv ancillaQubits systemQubits target))) =
      VerifiedCircuitCore.Circuit.gate (.x target)
  congr 1
  exact congrArg ReversibleGate.x
    ((analyticCanonicalWireEquiv ancillaQubits systemQubits).symm_apply_apply target)

/-- 共有coreのAND-chain compilerをQ wireへ移す再帰bridge。 -/
theorem compileCoreStageToReversibleGate_andChainUse
    {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits)
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.andChainUse
          (analyticCanonicalWireEquiv ancillaQubits systemQubits previous)
          (analyticWiresToCore controls) (analyticWiresToCore scratches)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
      ReversibleCircuit.andChainUse previous controls scratches target := by
  induction controls generalizing previous scratches with
  | nil =>
      simpa [analyticWiresToCore,
        VerifiedCircuitCore.ClassicalReversibleStage.andChainUse,
        ReversibleCircuit.andChainUse] using
        compileCoreStageToReversibleGate_safeXorControlled previous target
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil => rfl
      | cons scratch scratches =>
          simp only [analyticWiresToCore, List.map_cons,
            VerifiedCircuitCore.ClassicalReversibleStage.andChainUse,
            compileCoreStageToReversibleGate_seq,
            ReversibleCircuit.andChainUse]
          have tail := inductionHypothesis scratch scratches
          rw [show compileCoreStageToReversibleGate
              (VerifiedCircuitCore.ClassicalReversibleStage.andChainUse
                (analyticCanonicalWireEquiv ancillaQubits systemQubits scratch)
                (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) controls)
                (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) scratches)
                (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
              ReversibleCircuit.andChainUse scratch controls scratches target by
                simpa only [analyticWiresToCore] using tail]
          rw [compileCoreStageToReversibleGate_safeXorDoublyControlled]

/-- AND chain stageのcompilerは既存再帰constructorと一致する。 -/
theorem compile_andChainUse {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits)
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (andChainUse previous controls scratches target).compile =
      ReversibleCircuit.andChainUse previous controls scratches target := by
  rw [andChainUse, compile_ofCore]
  exact compileCoreStageToReversibleGate_andChainUse
    previous controls scratches target

/-- 共有coreのpositive multi-control compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_positiveMultiControlledX
    {ancillaQubits systemQubits : Nat}
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.positiveMultiControlledX
          (analyticWiresToCore controls) (analyticWiresToCore scratches)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
      ReversibleCircuit.positiveMultiControlledX controls scratches target := by
  cases controls with
  | nil =>
      simpa [analyticWiresToCore,
        VerifiedCircuitCore.ClassicalReversibleStage.positiveMultiControlledX,
        ReversibleCircuit.positiveMultiControlledX] using
        compileCoreStageToReversibleGate_xorOne target
  | cons first rest =>
      cases rest with
      | nil =>
          simpa [analyticWiresToCore,
            VerifiedCircuitCore.ClassicalReversibleStage.positiveMultiControlledX,
            ReversibleCircuit.positiveMultiControlledX] using
            compileCoreStageToReversibleGate_safeXorControlled first target
      | cons second remaining =>
          cases scratches with
          | nil => rfl
          | cons scratch scratches =>
              simp only [analyticWiresToCore, List.map_cons,
                VerifiedCircuitCore.ClassicalReversibleStage.positiveMultiControlledX,
                compileCoreStageToReversibleGate_seq,
                ReversibleCircuit.positiveMultiControlledX]
              rw [compileCoreStageToReversibleGate_safeXorDoublyControlled,
                show compileCoreStageToReversibleGate
                    (VerifiedCircuitCore.ClassicalReversibleStage.andChainUse
                      (analyticCanonicalWireEquiv ancillaQubits systemQubits scratch)
                      (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) remaining)
                      (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) scratches)
                      (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
                    ReversibleCircuit.andChainUse scratch remaining scratches target by
                      simpa only [analyticWiresToCore] using
                        compileCoreStageToReversibleGate_andChainUse
                          scratch remaining scratches target]

/-- positive multi-controlled X stageのcompilerは既存constructorと一致する。 -/
theorem compile_positiveMultiControlledX {ancillaQubits systemQubits : Nat}
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (positiveMultiControlledX controls scratches target).compile =
      ReversibleCircuit.positiveMultiControlledX controls scratches target := by
  rw [positiveMultiControlledX, compile_ofCore]
  exact compileCoreStageToReversibleGate_positiveMultiControlledX
    controls scratches target

/-- gate葉列のcore sequenceは同じgate列のfromListと一致する。 -/
theorem sequence_gate_eq_fromList {Gate : Type*} (gates : List Gate) :
    VerifiedCircuitCore.Circuit.sequence
        (gates.map VerifiedCircuitCore.Circuit.gate) =
      VerifiedCircuitCore.Circuit.fromList gates := by
  induction gates with
  | nil => rfl
  | cons gate gates inductionHypothesis =>
      simp only [List.map_cons, VerifiedCircuitCore.Circuit.sequence,
        VerifiedCircuitCore.Circuit.fromList, inductionHypothesis]

/-- 0-control wire抽出後のX写像は、既存gate filterMapと同じ列になる。 -/
theorem zeroControlWires_map_x {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    (zeroControlWires controls).map ReversibleGate.x =
      controls.filterMap fun control =>
        if control.2 then none else some (.x control.1) := by
  rw [zeroControlWires, analyticWiresOfCore_zeroControlWires]
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨wire, value⟩
      cases value <;> simp [inductionHypothesis]

/-- 共有coreの0-control反転列をQ wireへ移すcompiler bridge。 -/
theorem compileCoreStageToReversibleGate_invertZeroControls
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.invertZeroControls
          (analyticControlsToCore controls)) =
      ReversibleCircuit.invertZeroControls controls := by
  rw [VerifiedCircuitCore.ClassicalReversibleStage.invertZeroControls,
    compileCoreStageToReversibleGate_sequence]
  let selected := controls.filterMap fun control =>
    if control.2 then none else some control.1
  have coreWires :
      VerifiedCircuitCore.ClassicalReversibleStage.zeroControlWires
          (analyticControlsToCore controls) = analyticWiresToCore selected := by
    rw [← analyticWiresToCore_ofCore
      (VerifiedCircuitCore.ClassicalReversibleStage.zeroControlWires
        (analyticControlsToCore controls))]
    exact congrArg analyticWiresToCore
      (analyticWiresOfCore_zeroControlWires controls)
  have compiledSelected :
      List.map compileCoreStageToReversibleGate
          (List.map
            (fun wire =>
              VerifiedCircuitCore.ClassicalReversibleStage.instruction
                (VerifiedCircuitCore.ClassicalReversibleInstruction.xorOne wire))
            (analyticWiresToCore selected)) =
        selected.map fun wire =>
          VerifiedCircuitCore.Circuit.gate (ReversibleGate.x wire) := by
    simp only [analyticWiresToCore, List.map_map]
    apply List.map_congr_left
    intro wire _
    exact compileCoreStageToReversibleGate_xorOne wire
  rw [coreWires, compiledSelected]
  have remap :
      selected.map (fun wire =>
        VerifiedCircuitCore.Circuit.gate (ReversibleGate.x wire)) =
        (selected.map ReversibleGate.x).map
          VerifiedCircuitCore.Circuit.gate := by
    simp [List.map_map, Function.comp_def]
  rw [remap]
  rw [sequence_gate_eq_fromList, ReversibleCircuit.invertZeroControls]
  congr 1
  have selected_eq : selected = zeroControlWires controls := by
    rw [zeroControlWires, analyticWiresOfCore_zeroControlWires]
  rw [selected_eq]
  exact zeroControlWires_map_x controls

/-- 0-control反転stageのcompilerは既存X列constructorと一致する。 -/
theorem compile_invertZeroControls {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    (invertZeroControls controls).compile =
      ReversibleCircuit.invertZeroControls controls := by
  rw [invertZeroControls, compile_ofCore]
  exact compileCoreStageToReversibleGate_invertZeroControls controls

/-- 共有coreのBool multi-control compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_boolMultiControlledX
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.boolMultiControlledX
          (analyticControlsToCore controls) (analyticWiresToCore scratch)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
      ReversibleCircuit.boolMultiControlledX controls scratch target := by
  rw [VerifiedCircuitCore.ClassicalReversibleStage.boolMultiControlledX]
  rw [compileCoreStageToReversibleGate_seq,
    compileCoreStageToReversibleGate_invertZeroControls,
    compileCoreStageToReversibleGate_seq]
  rw [analyticControlsToCore_map_fst]
  rw [compileCoreStageToReversibleGate_positiveMultiControlledX,
    compileCoreStageToReversibleGate_invertZeroControls]
  rfl

/-- Bool multi-controlled X stageのcompilerは既存constructorと一致する。 -/
theorem compile_boolMultiControlledX {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (boolMultiControlledX controls scratch target).compile =
      ReversibleCircuit.boolMultiControlledX controls scratch target := by
  rw [boolMultiControlledX, compile_ofCore]
  exact compileCoreStageToReversibleGate_boolMultiControlledX
    controls scratch target

/-- XOR copy stageのcompilerは既存再帰constructorと一致する。 -/
theorem compile_xorCopy {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits)) :
    (xorCopy source target).compile = ReversibleCircuit.xorCopy source target := by
  induction source generalizing target with
  | nil => simp [xorCopy, ReversibleCircuit.xorCopy, compile]
  | cons source sources inductionHypothesis =>
      cases target with
      | nil => simp [xorCopy, ReversibleCircuit.xorCopy, compile]
      | cons target targets =>
          simp [xorCopy, ReversibleCircuit.xorCopy, compile,
            compile_safeXorControlled, inductionHypothesis]

/-- pure な controlled bit swap の compiler は既存正本と一致する。 -/
theorem compile_controlledSwapBit
    {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits) :
    (controlledSwapBit control left right).compile =
      ReversibleCircuit.controlledSwapBit control left right := by
  simp [controlledSwapBit, ReversibleCircuit.controlledSwapBit, compile,
    compile_safeXorControlled, compile_safeXorDoublyControlled]

/-- pure な controlled word swap の compiler は既存正本と一致する。 -/
theorem compile_controlledSwapWord
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits)) :
    (controlledSwapWord control left right).compile =
      ReversibleCircuit.controlledSwapWord control left right := by
  rw [controlledSwapWord, compile_sequence,
    ReversibleCircuit.controlledSwapWord]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro pair _
  exact compile_controlledSwapBit control pair.1 pair.2

/-- 共有coreのbit equality compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_computeBitEqual
    {ancillaQubits systemQubits : Nat}
    (left right flag : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.computeBitEqual
          (analyticCanonicalWireEquiv ancillaQubits systemQubits left)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits right)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits flag)) =
      ReversibleCircuit.computeBitEqual left right flag := by
  rw [VerifiedCircuitCore.ClassicalReversibleStage.computeBitEqual,
    compileCoreStageToReversibleGate_seq,
    compileCoreStageToReversibleGate_safeXorControlled,
    compileCoreStageToReversibleGate_seq,
    compileCoreStageToReversibleGate_safeXorControlled,
    compileCoreStageToReversibleGate_xorOne]
  rfl

/-- equality flag stageのcompilerは既存constructorと一致する。 -/
theorem compile_computeBitEqual {ancillaQubits systemQubits : Nat}
    (left right flag : Wire ancillaQubits systemQubits) :
    (computeBitEqual left right flag).compile =
      ReversibleCircuit.computeBitEqual left right flag := by
  rw [computeBitEqual, compile_ofCore]
  exact compileCoreStageToReversibleGate_computeBitEqual left right flag

/-- 共有coreのequality flag列compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_computeEqualityFlags
    {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits)) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.computeEqualityFlags
          (analyticWiresToCore left) (analyticWiresToCore right)
          (analyticWiresToCore flags)) =
      ReversibleCircuit.computeEqualityFlags left right flags := by
  rw [VerifiedCircuitCore.ClassicalReversibleStage.computeEqualityFlags,
    compileCoreStageToReversibleGate_sequence,
    ReversibleCircuit.computeEqualityFlags,
    analyticWiresToCore_zip3]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro entry _
  exact compileCoreStageToReversibleGate_computeBitEqual
    entry.1 entry.2.1 entry.2.2

/-- equality flag列stageのcompilerは既存有限sequenceと一致する。 -/
theorem compile_computeEqualityFlags {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits)) :
    (computeEqualityFlags left right flags).compile =
      ReversibleCircuit.computeEqualityFlags left right flags := by
  rw [computeEqualityFlags, compile_ofCore]
  exact compileCoreStageToReversibleGate_computeEqualityFlags left right flags

/-- 共有coreのword equality compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_xorEqualityIntoTarget
    {ancillaQubits systemQubits : Nat}
    (left right flags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.xorEqualityIntoTarget
          (analyticWiresToCore left) (analyticWiresToCore right)
          (analyticWiresToCore flags) (analyticWiresToCore scratch)
          (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
      ReversibleCircuit.xorEqualityIntoTargetCircuit
        left right flags scratch target := by
  rw [VerifiedCircuitCore.ClassicalReversibleStage.xorEqualityIntoTarget,
    VerifiedCircuitCore.ClassicalReversibleStage.computeUseUncompute,
    compileCoreStageToReversibleGate_seq,
    compileCoreStageToReversibleGate_computeEqualityFlags,
    compileCoreStageToReversibleGate_seq,
    compileCoreStageToReversibleGate_positiveMultiControlledX,
    compileCoreStageToReversibleGate_reverse,
    compileCoreStageToReversibleGate_computeEqualityFlags]
  rfl

/-- equality target stageのcompilerは既存compute--use--uncompute constructorと一致する。 -/
theorem compile_xorEqualityIntoTarget {ancillaQubits systemQubits : Nat}
    (left right flags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (xorEqualityIntoTarget left right flags scratch target).compile =
      ReversibleCircuit.xorEqualityIntoTargetCircuit left right flags scratch target := by
  rw [xorEqualityIntoTarget, compile_ofCore]
  exact compileCoreStageToReversibleGate_xorEqualityIntoTarget
    left right flags scratch target

/-- pure less-than control programは既存control programと同じ列である。 -/
theorem lessThanControlProgram_eq {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits)) :
    lessThanControlProgram left right equalFlags =
      ReversibleCircuit.lessThanControlProgram left right equalFlags := by
  induction left generalizing right equalFlags with
  | nil => rfl
  | cons left lefts inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons right rights =>
          simp [lessThanControlProgram, ReversibleCircuit.lessThanControlProgram,
            inductionHypothesis]

/-- unsigned less-than stageのcompilerは既存比較回路と一致する。 -/
theorem compile_xorLessThanIntoTarget {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (xorLessThanIntoTarget left right equalFlags scratch target).compile =
      ReversibleCircuit.xorLessThanIntoTargetCircuit
        left right equalFlags scratch target := by
  have branchesEqual :
      (sequence <| (lessThanControlProgram left right equalFlags).map fun controls =>
        boolMultiControlledX controls scratch target).compile =
      VerifiedCircuitCore.Circuit.sequence
        ((ReversibleCircuit.lessThanControlProgram left right equalFlags).map
          fun controls => ReversibleCircuit.boolMultiControlledX controls scratch target) := by
    rw [compile_sequence]
    rw [lessThanControlProgram_eq]
    apply congrArg VerifiedCircuitCore.Circuit.sequence
    rw [List.map_map]
    apply List.map_congr_left
    intro controls _
    exact compile_boolMultiControlledX controls scratch target
  rw [xorLessThanIntoTarget, ReversibleCircuit.xorLessThanIntoTargetCircuit]
  rw [TotalReversibleStage.compile]
  rw [TotalReversibleStage.compile]
  rw [compile_computeEqualityFlags]
  rw [branchesEqual]
  rw [compile_reverse]
  rw [compile_computeEqualityFlags]

/-- 共有coreのincrement carry列compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_incrementCarrySequence
    {ancillaQubits systemQubits : Nat}
    (lower word scratch : List (Wire ancillaQubits systemQubits)) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.incrementCarrySequence
          (analyticWiresToCore lower) (analyticWiresToCore word)
          (analyticWiresToCore scratch)) =
      ReversibleCircuit.incrementWordCarrySequenceCircuit lower word scratch := by
  induction word generalizing lower with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      simp only [analyticWiresToCore, List.map_cons,
        VerifiedCircuitCore.ClassicalReversibleStage.incrementCarrySequence,
        compileCoreStageToReversibleGate_seq,
        ReversibleCircuit.incrementWordCarrySequenceCircuit]
      have tail := inductionHypothesis (lower ++ [target])
      rw [show compileCoreStageToReversibleGate
          (VerifiedCircuitCore.ClassicalReversibleStage.incrementCarrySequence
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) lower ++
              [analyticCanonicalWireEquiv ancillaQubits systemQubits target])
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) higher)
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) scratch)) =
          ReversibleCircuit.incrementWordCarrySequenceCircuit
            (lower ++ [target]) higher scratch by
            simpa only [analyticWiresToCore, List.map_append, List.map_cons,
              List.map_nil] using tail]
      rw [show compileCoreStageToReversibleGate
          (VerifiedCircuitCore.ClassicalReversibleStage.positiveMultiControlledX
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) lower)
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) scratch)
            (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
          ReversibleCircuit.positiveMultiControlledX lower scratch target by
            simpa only [analyticWiresToCore] using
              compileCoreStageToReversibleGate_positiveMultiControlledX
                lower scratch target]

/-- carry列stageのcompilerは既存increment内部constructorと一致する。 -/
theorem compile_incrementCarrySequence {ancillaQubits systemQubits : Nat}
    (lower word scratch : List (Wire ancillaQubits systemQubits)) :
    (incrementCarrySequence lower word scratch).compile =
      ReversibleCircuit.incrementWordCarrySequenceCircuit lower word scratch := by
  rw [incrementCarrySequence, compile_ofCore]
  exact compileCoreStageToReversibleGate_incrementCarrySequence
    lower word scratch

/-- 全dirty increment stageのcompilerは既存increment回路と一致する。 -/
theorem compile_incrementWordMod2PowInPlace {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) :
    (incrementWordMod2PowInPlace word scratch).compile =
      ReversibleCircuit.incrementWordMod2PowInPlaceCircuit word scratch := by
  rw [incrementWordMod2PowInPlace, compile_ofCore]
  simpa only [VerifiedCircuitCore.ClassicalReversibleStage.incrementWordMod2PowInPlace,
    ReversibleCircuit.incrementWordMod2PowInPlaceCircuit,
    analyticWiresToCore, List.map_nil] using
      compileCoreStageToReversibleGate_incrementCarrySequence [] word scratch

/-- 共有coreのdecrement borrow列compilerをQ wireへ移すbridge。 -/
theorem compileCoreStageToReversibleGate_decrementBorrowSequence
    {ancillaQubits systemQubits : Nat}
    (lower word scratch : List (Wire ancillaQubits systemQubits)) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.decrementBorrowSequence
          (analyticWiresToCore lower) (analyticWiresToCore word)
          (analyticWiresToCore scratch)) =
      ReversibleCircuit.decrementWordBorrowSequenceCircuit lower word scratch := by
  induction word generalizing lower with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      simp only [analyticWiresToCore, List.map_cons,
        VerifiedCircuitCore.ClassicalReversibleStage.decrementBorrowSequence,
        compileCoreStageToReversibleGate_seq,
        ReversibleCircuit.decrementWordBorrowSequenceCircuit]
      have tail := inductionHypothesis (lower ++ [target])
      rw [show compileCoreStageToReversibleGate
          (VerifiedCircuitCore.ClassicalReversibleStage.decrementBorrowSequence
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) lower ++
              [analyticCanonicalWireEquiv ancillaQubits systemQubits target])
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) higher)
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) scratch)) =
          ReversibleCircuit.decrementWordBorrowSequenceCircuit
            (lower ++ [target]) higher scratch by
            simpa only [analyticWiresToCore, List.map_append, List.map_cons,
              List.map_nil] using tail]
      have controlsMap :
          (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) lower).map
              (fun wire => (wire, false)) =
            analyticControlsToCore (lower.map fun wire => (wire, false)) := by
        simp [analyticControlsToCore, List.map_map, Function.comp_def]
      rw [controlsMap]
      rw [show compileCoreStageToReversibleGate
          (VerifiedCircuitCore.ClassicalReversibleStage.boolMultiControlledX
            (analyticControlsToCore (lower.map fun wire => (wire, false)))
            (List.map (analyticCanonicalWireEquiv ancillaQubits systemQubits) scratch)
            (analyticCanonicalWireEquiv ancillaQubits systemQubits target)) =
          ReversibleCircuit.boolMultiControlledX
            (lower.map fun wire => (wire, false)) scratch target by
            simpa only [analyticWiresToCore] using
              compileCoreStageToReversibleGate_boolMultiControlledX
                (lower.map fun wire => (wire, false)) scratch target]

/-- borrow列stageのcompilerは既存decrement内部constructorと一致する。 -/
theorem compile_decrementBorrowSequence {ancillaQubits systemQubits : Nat}
    (lower word scratch : List (Wire ancillaQubits systemQubits)) :
    (decrementBorrowSequence lower word scratch).compile =
      ReversibleCircuit.decrementWordBorrowSequenceCircuit lower word scratch := by
  rw [decrementBorrowSequence, compile_ofCore]
  exact compileCoreStageToReversibleGate_decrementBorrowSequence
    lower word scratch

/-- 全dirty decrement stageのcompilerは既存decrement回路と一致する。 -/
theorem compile_decrementWordMod2PowInPlace {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) :
    (decrementWordMod2PowInPlace word scratch).compile =
      ReversibleCircuit.decrementWordMod2PowInPlaceCircuit word scratch := by
  rw [decrementWordMod2PowInPlace, compile_ofCore]
  simpa only [VerifiedCircuitCore.ClassicalReversibleStage.decrementWordMod2PowInPlace,
    ReversibleCircuit.decrementWordMod2PowInPlaceCircuit,
    analyticWiresToCore, List.map_nil] using
      compileCoreStageToReversibleGate_decrementBorrowSequence [] word scratch

end TotalReversibleStage

end ProbabilityGeneratorQProof
