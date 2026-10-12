import QLean.Generator.Implementation.UniformPreparationCircuit

/-!
# 一般幅の可逆論理・算術回路

可逆oracleで再利用するXOR copy、定数XOR、多重制御AND、word等値、unsigned比較、
周期increment/decrement、controlled swapを、`X/CNOT/Toffoli`だけで構成する。
全constructorは任意の入力リストに対して全域であり、wire衝突時は恒等回路へ安全に退避する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- X基底作用を標的wireで読むと入力bitの否定になる。 -/
@[simp] theorem xBasisAction_target
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    xBasisAction target input target = !(input target) := by
  simp [xBasisAction]

/-- X基底作用は標的以外のwireを変更しない。 -/
@[simp] theorem xBasisAction_other
    {ancillaQubits systemQubits : Nat}
    (target wire : Wire ancillaQubits systemQubits)
    (different : wire ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    xBasisAction target input wire = input wire := by
  simp [xBasisAction, different]

/-- CNOT基底作用を標的wireで読むと、制御bitが1のときだけ反転する。 -/
@[simp] theorem cnotBasisAction_target
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    cnotBasisAction control target input target =
      if input control then !(input target) else input target := by
  simp [cnotBasisAction]

/-- CNOT基底作用は標的以外のwireを変更しない。 -/
@[simp] theorem cnotBasisAction_other
    {ancillaQubits systemQubits : Nat}
    (control target wire : Wire ancillaQubits systemQubits)
    (different : wire ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    cnotBasisAction control target input wire = input wire := by
  simp [cnotBasisAction, different]

/-- Toffoli基底作用を標的wireで読むと、二制御bitがともに1のときだけ反転する。 -/
@[simp] theorem toffoliBasisAction_target
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    toffoliBasisAction control₁ control₂ target input target =
      if input control₁ && input control₂ then !(input target) else input target := by
  simp [toffoliBasisAction]

/-- Toffoli基底作用は標的以外のwireを変更しない。 -/
@[simp] theorem toffoliBasisAction_other
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target wire : Wire ancillaQubits systemQubits)
    (different : wire ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    toffoliBasisAction control₁ control₂ target input wire = input wire := by
  simp [toffoliBasisAction, different]

/-- 可逆回路の逐次合成は、第一回路の基底作用後に第二回路を作用させる。 -/
@[simp] theorem runBasis_seq
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (first second : Circuit Gate) (input : basis) :
    Circuit.runBasis gatePermutation (Circuit.seq first second) input =
      second.runBasis gatePermutation (first.runBasis gatePermutation input) := by
  simp [Circuit.runBasis,
    VerifiedCircuitCore.Circuit.runBasis,
    VerifiedCircuitCore.Circuit.toExecutionPermutation]

/-- 共有core名で現れた恒等回路も計算基底を変更しない。 -/
@[simp] theorem runBasis_core_identity
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (input : basis) :
    VerifiedCircuitCore.Circuit.runBasis gatePermutation
        (.identity : VerifiedCircuitCore.Circuit Gate) input = input := by
  rfl

/-- 共有coreの空sequenceも恒等回路として計算基底を変更しない。 -/
@[simp] theorem runBasis_core_sequence_nil
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (input : basis) :
    VerifiedCircuitCore.Circuit.runBasis gatePermutation
        (VerifiedCircuitCore.Circuit.sequence []) input = input := by
  rfl

/-- Q互換名でcoreの非空sequenceを実行しても先頭から順に作用する。 -/
@[simp] theorem runBasis_local_core_sequence_cons
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (head : Circuit Gate) (tail : List (Circuit Gate)) (input : basis) :
    Circuit.runBasis gatePermutation
        (VerifiedCircuitCore.Circuit.sequence (head :: tail)) input =
      Circuit.runBasis gatePermutation (VerifiedCircuitCore.Circuit.sequence tail)
        (Circuit.runBasis gatePermutation head input) := by
  rfl

/-- 共有core名で現れた二項逐次回路も実行順の関数合成になる。 -/
@[simp] theorem runBasis_core_seq
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (first second : VerifiedCircuitCore.Circuit Gate) (input : basis) :
    VerifiedCircuitCore.Circuit.runBasis gatePermutation (.seq first second) input =
      VerifiedCircuitCore.Circuit.runBasis gatePermutation second
        (VerifiedCircuitCore.Circuit.runBasis gatePermutation first input) := by
  rfl

/-- Q互換名の基底実行と共有core名の基底実行は同じ関数である。 -/
theorem runBasis_core_eq_local
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (circuit : Circuit Gate) (input : basis) :
    VerifiedCircuitCore.Circuit.runBasis gatePermutation circuit input =
      Circuit.runBasis gatePermutation circuit input := by
  rfl

/-- X葉の基底作用は指定wireだけを反転する`xBasisAction`である。 -/
@[simp] theorem runBasis_x
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    (.gate (.x target) : Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation input = xBasisAction target input := by
  rfl

/-- Q互換名で現れたX葉も指定wireだけを反転する。 -/
@[simp] theorem runBasis_local_x
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    Circuit.runBasis reversibleGatePermutation
        (.gate (.x target) : Circuit (ReversibleGate ancillaQubits systemQubits)) input =
      xBasisAction target input := by
  rfl

/-- CNOT葉の基底作用は`cnotBasisAction`である。 -/
@[simp] theorem runBasis_cnot
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    (.gate (.cnot control target different) :
      Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation input = cnotBasisAction control target input := by
  rfl

/-- Toffoli葉の基底作用は`toffoliBasisAction`である。 -/
@[simp] theorem runBasis_toffoli
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    (.gate (.toffoli control₁ control₂ target controlsDifferent firstDifferent
      secondDifferent) : Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation input =
      toffoliBasisAction control₁ control₂ target input := by
  rfl

/-- wireが異なる場合だけCNOTを生成する可逆回路用の全域constructor。 -/
def safeCnot {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  if different : control ≠ target then
    .gate (.cnot control target different)
  else
    .identity

/-- 相異なるwireに対するsafe CNOTは通常のCNOT基底作用と一致する。 -/
theorem runBasis_safeCnot
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    (safeCnot control target).runBasis reversibleGatePermutation input =
      cnotBasisAction control target input := by
  simp [safeCnot, different, Circuit.runBasis]

/-- Q互換名で現れたsafe CNOTも通常のCNOT基底作用と一致する。 -/
theorem runBasis_local_safeCnot
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    Circuit.runBasis reversibleGatePermutation (safeCnot control target) input =
      cnotBasisAction control target input := by
  exact runBasis_safeCnot control target different input

/-- 三wireが相異なる場合だけToffoliを生成する可逆回路用の全域constructor。 -/
def safeToffoli {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  if controlsDifferent : control₁ ≠ control₂ then
    if firstDifferent : control₁ ≠ target then
      if secondDifferent : control₂ ≠ target then
        .gate (.toffoli control₁ control₂ target controlsDifferent
          firstDifferent secondDifferent)
      else
        .identity
    else
      .identity
  else
    .identity

/-- 三本の相異なるwireに対するsafe Toffoliは通常のToffoli基底作用と一致する。 -/
theorem runBasis_safeToffoli
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    (safeToffoli control₁ control₂ target).runBasis
        reversibleGatePermutation input =
      toffoliBasisAction control₁ control₂ target input := by
  simp [safeToffoli, controlsDifferent, firstDifferent, secondDifferent,
    Circuit.runBasis]

/-- 共有core名で現れたsafe Toffoliも通常のToffoli基底作用と一致する。 -/
theorem runBasis_core_safeToffoli
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
        (safeToffoli control₁ control₂ target) input =
      toffoliBasisAction control₁ control₂ target input := by
  exact runBasis_safeToffoli control₁ control₂ target controlsDifferent
    firstDifferent secondDifferent input

/-- Q互換名で現れたsafe Toffoliも通常のToffoli基底作用と一致する。 -/
theorem runBasis_local_safeToffoli
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    Circuit.runBasis reversibleGatePermutation
        (safeToffoli control₁ control₂ target) input =
      toffoliBasisAction control₁ control₂ target input := by
  exact runBasis_safeToffoli control₁ control₂ target controlsDifferent
    firstDifferent secondDifferent input

/-- Bool制御値0のwireだけを反転する可逆X列。 -/
def invertZeroControls {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.fromList <| controls.filterMap fun control =>
    if control.2 then none else some (.x control.1)

/-- 途中まで計算したANDを延長し、target使用後に全scratchを逆計算する。 -/
def andChainUse {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits) :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits →
    Circuit (ReversibleGate ancillaQubits systemQubits)
  | [], _, target => safeCnot previous target
  | control :: controls, scratch :: scratches, target =>
      let step := safeToffoli previous control scratch
      .seq step <| .seq (andChainUse scratch controls scratches target) step
  | _ :: _, [], _ => .identity

/-- 全制御が1のときだけtargetを反転し、AND scratchを0へ戻す。 -/
def positiveMultiControlledX {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits →
    Circuit (ReversibleGate ancillaQubits systemQubits)
  | [], _, target => .gate (.x target)
  | [control], _, target => safeCnot control target
  | control₁ :: control₂ :: controls, scratch :: scratches, target =>
      let first := safeToffoli control₁ control₂ scratch
      .seq first <| .seq (andChainUse scratch controls scratches target) first
  | _ :: _ :: _, [], _ => .identity

/-- 0-controlを前後のXへ変換したBool値付き多重制御X。 -/
def boolMultiControlledX {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let invert := invertZeroControls controls
  .seq invert <| .seq
    (positiveMultiControlledX (controls.map Prod.fst) scratch target) invert

/-- 全下位bitが1のときだけ指定bitへXORする、increment carry stepの作用名付き回路。 -/
def xorAllLowerBitsOneIntoBitCircuit {ancillaQubits systemQubits : Nat}
    (lower scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  positiveMultiControlledX lower scratch target

/-- 全下位bitが0のときだけ指定bitへXORする、decrement borrow stepの作用名付き回路。 -/
def xorAllLowerBitsZeroIntoBitCircuit {ancillaQubits systemQubits : Nat}
    (lower scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  boolMultiControlledX (lower.map fun wire => (wire, false)) scratch target

/-- 二つの同長registerを対応wireごとに`target ^= source`としてXOR copyする。 -/
def xorCopy {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Circuit (ReversibleGate ancillaQubits systemQubits)
  | source :: sources, target :: targets =>
      .seq (safeCnot source target) (xorCopy sources targets)
  | _, _ => .identity

/-- Nat定数のlittle-endian bitが1の位置だけregisterへXORする。 -/
def xorConstant {ancillaQubits systemQubits : Nat}
    (register : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.fromList <| register.zipIdx.filterMap fun indexed =>
    if constant.testBit indexed.2 then some (.x indexed.1) else none

/-- 二bitの一致値`!(left XOR right)`を初期0のflagへ計算する。 -/
def computeBitEqual {ancillaQubits systemQubits : Nat}
    (left right flag : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  .seq (safeCnot left flag) <|
  .seq (safeCnot right flag) <|
  .gate (.x flag)

/-- 各bitの一致flagを並列に計算する回路。 -/
def computeEqualityFlags {ancillaQubits systemQubits : Nat}
    (left right flags : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| (left.zip (right.zip flags)).map fun entry =>
    computeBitEqual entry.1 entry.2.1 entry.2.2

/-- 二wordが等しいときだけtargetをXORし、全一致flagを0へ戻す。 -/
def xorEqualityIntoTargetCircuit {ancillaQubits systemQubits : Nat}
    (left right flags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let compute := computeEqualityFlags left right flags
  let use := positiveMultiControlledX flags scratch target
  .seq compute <| .seq use (compute.reverse id)

/--
little-endian wordの指定bitで`left=0,right=1`かつ上位bit一致を検査するBool制御列。
-/
def lessThanBranchControls {ancillaQubits systemQubits : Nat}
    (left right equalFlags : List (Wire ancillaQubits systemQubits))
    (index : Nat) : Option (List (Wire ancillaQubits systemQubits × Bool)) :=
  match left[index]?, right[index]? with
  | some leftBit, some rightBit =>
      let higherEqual := (equalFlags.drop (index + 1)).map fun wire => (wire, true)
      some ((leftBit, false) :: (rightBit, true) :: higherEqual)
  | _, _ => none

/-- little-endian比較の全bit位置に対応する有効なBool制御列。 -/
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

/-- little-endian wordの指定bitに対応する一個の比較分岐回路。 -/
def lessThanBranch {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (index : Nat) (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  match lessThanBranchControls left right equalFlags index with
  | some controls => boolMultiControlledX controls scratch target
  | none => .identity

/-- unsigned little-endian比較`target ^= (left < right)`を計算し、比較workを0へ戻す。 -/
def xorLessThanIntoTargetCircuit {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let compute := computeEqualityFlags left right equalFlags
  let branches := Circuit.sequence <|
    (lessThanControlProgram left right equalFlags).map fun controls =>
      boolMultiControlledX controls scratch target
  .seq compute <| .seq branches (compute.reverse id)

/-- 一bitのcontrolled swapを三個のCNOT/Toffoliへ分解する。 -/
def controlledSwapBit {ancillaQubits systemQubits : Nat}
    (control left right : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  .seq (safeCnot left right) <|
  .seq (safeToffoli control right left) <|
  safeCnot left right

/-- controlが1のとき二wordをbitwise swapする。 -/
def controlledSwapWord {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| (left.zip right).map fun pair =>
    controlledSwapBit control pair.1 pair.2

/-- incrementの一bitを、元の全下位bitが1という条件で反転する。 -/
def incrementAt {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) (index : Nat) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  match word[index]? with
  | some target =>
      positiveMultiControlledX (word.take index) scratch target
  | none => .identity

/-- 既知の下位wire列を制御として上位側からincrement反転を並べる内部回路。 -/
def incrementWordCarrySequenceCircuit {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Circuit (ReversibleGate ancillaQubits systemQubits)
  | _, [], _ => .identity
  | lower, target :: higher, scratch =>
      .seq (incrementWordCarrySequenceCircuit (lower ++ [target]) higher scratch)
        (positiveMultiControlledX lower scratch target)

/-- 幅に依存せず全modulo wrappingを含むlittle-endian周期increment。 -/
def incrementWordMod2PowInPlaceCircuit {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  incrementWordCarrySequenceCircuit [] word scratch

/-- decrementの一bitを、元の全下位bitが0という条件で反転する。 -/
def decrementAt {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) (index : Nat) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  match word[index]? with
  | some target =>
      boolMultiControlledX ((word.take index).map fun wire => (wire, false))
        scratch target
  | none => .identity

/-- 既知の下位wire列を0制御として上位側からdecrement反転を並べる内部回路。 -/
def decrementWordBorrowSequenceCircuit {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Circuit (ReversibleGate ancillaQubits systemQubits)
  | _, [], _ => .identity
  | lower, target :: higher, scratch =>
      .seq (decrementWordBorrowSequenceCircuit (lower ++ [target]) higher scratch)
        (boolMultiControlledX (lower.map fun wire => (wire, false)) scratch target)

/-- 幅に依存せず全modulo wrappingを含むlittle-endian周期decrement。 -/
def decrementWordMod2PowInPlaceCircuit {ancillaQubits systemQubits : Nat}
    (word scratch : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  decrementWordBorrowSequenceCircuit [] word scratch

/-- 可逆算術部品を正本の許可基本ゲート回路へ翻訳する。 -/
def toPrimitive {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits)) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  circuit.map ReversibleGate.toPrimitive

/-- 可逆算術部品を翻訳した回路の全葉は許可した五種類だけである。 -/
theorem toPrimitive_leaves {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits)) :
    ∀ gate ∈ (toPrimitive circuit).flatten, IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

/-- 可逆算術部品の翻訳後行列意味論は、その基底置換行列と一致する。 -/
theorem toPrimitive_operator_eq_permMatrix
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits)) :
    (toPrimitive circuit).toIdealOperator primitiveGateOperator =
      (circuit.toBasisPermutation reversibleGatePermutation).permMatrix ℂ :=
  reversibleCircuit_operator_eq_permMatrix circuit

end ReversibleCircuit

end ProbabilityGeneratorQProof
