import QLean.Generator.Analysis.ClassicalReversibleStageAdapter

/-!
# 可逆局所programの全dirty純粋stage

wire衝突時の恒等退避を含め、X・CNOT・Toffoliだけからなる再利用可能な
局所programを実装から独立に定義する。
-/

namespace ProbabilityGeneratorQProof

namespace TotalReversibleStage

/-- wireが異なるときだけcontrolled XORを追加する。 -/
def safeXorControlled {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled
    (analyticCanonicalWireEquiv ancillaQubits systemQubits control)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits target)

/-- 三wireが相異なるときだけdoubly-controlled XORを追加する。 -/
def safeXorDoublyControlled {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled
    (analyticCanonicalWireEquiv ancillaQubits systemQubits control₁)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits control₂)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits target)

/-- Bool値0のcontrolから反転対象wireだけを取り出す。 -/
def zeroControlWires {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    List (Wire ancillaQubits systemQubits) :=
  analyticWiresOfCore <|
    VerifiedCircuitCore.ClassicalReversibleStage.zeroControlWires
      (analyticControlsToCore controls)

/-- Bool値0のcontrolだけを前処理・後処理するX stage列。 -/
def invertZeroControls {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.invertZeroControls
    (analyticControlsToCore controls)

/-- 途中まで計算したANDを延長し、使用後に逆計算する。 -/
def andChainUse {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits) :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits →
    TotalReversibleStage ancillaQubits systemQubits
  | controls, scratches, target =>
      ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.andChainUse
        (analyticCanonicalWireEquiv ancillaQubits systemQubits previous)
        (analyticWiresToCore controls) (analyticWiresToCore scratches)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target)

/-- 全controlが1のときだけtargetを反転し、AND scratchを逆計算する。 -/
def positiveMultiControlledX {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits →
    TotalReversibleStage ancillaQubits systemQubits
  | controls, scratches, target =>
      ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.positiveMultiControlledX
        (analyticWiresToCore controls) (analyticWiresToCore scratches)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target)

/-- 0-controlの前後反転を含むBool値付き多重制御X。 -/
def boolMultiControlledX {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.boolMultiControlledX
    (analyticControlsToCore controls) (analyticWiresToCore scratch)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits target)

/-- 対応するsource bitをtarget bitへ順にXORする。 -/
def xorCopy {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    TotalReversibleStage ancillaQubits systemQubits
  | source :: sources, target :: targets =>
      .seq (safeXorControlled source target) (xorCopy sources targets)
  | _, _ => .identity

/-- The Q raw-copy stage is exactly the shared collision-safe, zip-truncating
raw-copy stage after canonical wire reindexing. -/
theorem toCore_xorCopy_eq_rawXorCopy {ancillaQubits systemQubits : Nat}
    (sources targets : List (Wire ancillaQubits systemQubits)) :
    (xorCopy sources targets).toCore =
      VerifiedCircuitCore.ClassicalReversibleStage.rawXorCopy
        (analyticWiresToCore sources) (analyticWiresToCore targets) := by
  induction sources generalizing targets with
  | nil => simp [xorCopy, analyticWiresToCore,
      VerifiedCircuitCore.ClassicalReversibleStage.rawXorCopy,
      TotalReversibleStage.toCore]
  | cons source sources inductionHypothesis =>
      cases targets with
      | nil => simp [xorCopy, analyticWiresToCore,
          VerifiedCircuitCore.ClassicalReversibleStage.rawXorCopy,
          TotalReversibleStage.toCore]
      | cons target targets =>
          simp [xorCopy, analyticWiresToCore,
            VerifiedCircuitCore.ClassicalReversibleStage.rawXorCopy,
            safeXorControlled, TotalReversibleStage.toCore,
            inductionHypothesis]

/-- A raw Q XOR copy preserves every wire outside its target list.  The proof
is only the JointBasis/canonical-wire transport of the shared-core theorem. -/
theorem xorCopy_reference_apply_outside_target
    {ancillaQubits systemQubits : Nat}
    (sources targets : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ targets) :
    (xorCopy sources targets).reference input wire = input wire := by
  have coreOutside :
      analyticCanonicalWireEquiv ancillaQubits systemQubits wire ∉
        analyticWiresToCore targets := by
    simpa [analyticWiresToCore] using outside
  have coreResult :=
    VerifiedCircuitCore.ClassicalReversibleStage.rawXorCopy_reference_apply_outside_target
      (analyticWiresToCore sources) (analyticWiresToCore targets)
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
      (analyticCanonicalWireEquiv ancillaQubits systemQubits wire) coreOutside
  rw [← toCore_xorCopy_eq_rawXorCopy sources targets,
    TotalReversibleStage.toCore_reference_apply] at coreResult
  simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using coreResult

/-- 一つの control の下で二つの bit を swap する三段操作。 -/
def controlledSwapBit {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  .seq (safeXorControlled left right) <|
    .seq (safeXorDoublyControlled control right left) <|
      safeXorControlled left right

/-- Canonical shared-core image of one Q controlled-swap bit stage. -/
def controlledSwapBitCore {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits) :
    VerifiedCircuitCore.ClassicalReversibleStage (ancillaQubits + systemQubits) :=
  .seq
    (VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled
      (analyticCanonicalWireEquiv ancillaQubits systemQubits left)
      (analyticCanonicalWireEquiv ancillaQubits systemQubits right)) <|
    .seq
      (VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled
        (analyticCanonicalWireEquiv ancillaQubits systemQubits control)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits right)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits left)) <|
      VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled
        (analyticCanonicalWireEquiv ancillaQubits systemQubits left)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits right)

/-- The Q-to-core adapter preserves the complete one-bit Fredkin stage AST. -/
theorem toCore_controlledSwapBit {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits) :
    (controlledSwapBit control left right).toCore =
      controlledSwapBitCore control left right := by
  simp [controlledSwapBit, controlledSwapBitCore,
    safeXorControlled, safeXorDoublyControlled,
    TotalReversibleStage.toCore]

/-- 一つの control の下で、対応する二つの word bit を順に swap する。 -/
def controlledSwapWord {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  sequence <| (left.zip right).map fun pair =>
    controlledSwapBit control pair.1 pair.2

/-- Canonical shared-core image of a Q controlled-register swap program. -/
def controlledSwapWordCore {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits)) :
    VerifiedCircuitCore.ClassicalReversibleStage (ancillaQubits + systemQubits) :=
  VerifiedCircuitCore.ClassicalReversibleStage.sequence <|
    (left.zip right).map fun pair =>
      controlledSwapBitCore control pair.1 pair.2

/-- The Q-to-core adapter preserves the complete controlled-register-swap AST. -/
theorem toCore_controlledSwapWord {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits)) :
    (controlledSwapWord control left right).toCore =
      controlledSwapWordCore control left right := by
  rw [controlledSwapWord, TotalReversibleStage.toCore_sequence]
  unfold controlledSwapWordCore
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro pair _
  exact toCore_controlledSwapBit control pair.1 pair.2

/-- Nat定数の1-bit位置だけを反転する。 -/
def xorConstant {ancillaQubits systemQubits : Nat}
    (register : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.xorConstant
    (analyticWiresToCore register) constant

/-- 二bitの一致値を一つのflagへXORする三段stage。 -/
def computeBitEqual {ancillaQubits systemQubits : Nat}
    (left right flag : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.computeBitEqual
    (analyticCanonicalWireEquiv ancillaQubits systemQubits left)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits right)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits flag)

/-- 各bitの一致flagを順に計算する。 -/
def computeEqualityFlags {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.computeEqualityFlags
    (analyticWiresToCore left) (analyticWiresToCore right)
    (analyticWiresToCore flags)

/-- 二wordが等しいときだけtargetをXORし、一致flagを逆計算する。 -/
def xorEqualityIntoTarget {ancillaQubits systemQubits : Nat}
    (left right flags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.xorEqualityIntoTarget
    (analyticWiresToCore left) (analyticWiresToCore right)
    (analyticWiresToCore flags) (analyticWiresToCore scratch)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits target)

/-- little-endian比較の各bit位置に対応するBool制御列。 -/
def lessThanControlProgram {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (List (Wire ancillaQubits systemQubits × Bool))
  | leftBit :: left, rightBit :: right, equalFlags =>
      let higherEqual := (equalFlags.drop 1).map fun wire => (wire, true)
      ((leftBit, false) :: (rightBit, true) :: higherEqual) ::
        lessThanControlProgram left right (equalFlags.drop 1)
  | _, _, _ => []

/-- unsigned little-endian比較をtargetへXORし、一致flagを逆計算する。 -/
def xorLessThanIntoTarget {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  let compute := computeEqualityFlags left right equalFlags
  let branches := sequence <|
    (lessThanControlProgram left right equalFlags).map fun controls =>
      boolMultiControlledX controls scratch target
  .seq compute <| .seq branches compute.reverse

/-- 上位側からcarry条件を順に作用させるincrement stage。 -/
def incrementCarrySequence {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    TotalReversibleStage ancillaQubits systemQubits
  | lower, higher, scratch =>
      ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.incrementCarrySequence
        (analyticWiresToCore lower) (analyticWiresToCore higher)
        (analyticWiresToCore scratch)

/-- little-endian wordの全dirty周期increment stage。 -/
def incrementWordMod2PowInPlace {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.incrementWordMod2PowInPlace
    (analyticWiresToCore word) (analyticWiresToCore scratch)

/-- 上位側からborrow条件を順に作用させるdecrement stage。 -/
def decrementBorrowSequence {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    TotalReversibleStage ancillaQubits systemQubits
  | lower, higher, scratch =>
      ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.decrementBorrowSequence
        (analyticWiresToCore lower) (analyticWiresToCore higher)
        (analyticWiresToCore scratch)

/-- little-endian wordの全dirty周期decrement stage。 -/
def decrementWordMod2PowInPlace {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  ofCore <| VerifiedCircuitCore.ClassicalReversibleStage.decrementWordMod2PowInPlace
    (analyticWiresToCore word) (analyticWiresToCore scratch)

end TotalReversibleStage

end ProbabilityGeneratorQProof
