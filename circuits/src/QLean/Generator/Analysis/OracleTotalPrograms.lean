import QLean.Generator.Analysis.TotalReversiblePrograms
import QLean.Generator.Analysis.QParameters

/-!
# oracle局所writerの全dirty純粋stage

selector定数比較、制御copy、制御定数XORを、独立stageとして定義する。
-/

namespace ProbabilityGeneratorQProof

namespace OracleTotalProgram

/-- selector定数比較のBool制御列を指定bit位置から作る。 -/
def selectorConstantControlsAux
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat) :
    List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits × Bool)
  | [] => []
  | wire :: wires =>
      (wire, constant.testBit start) ::
        selectorConstantControlsAux constant (start + 1) wires

/-- selector定数比較のlittle-endian Bool制御列。 -/
def selectorConstantControls
    {ancillaQubits systemQubits : Nat}
    (selector : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    List (Wire ancillaQubits systemQubits × Bool) :=
  selectorConstantControlsAux constant 0 selector

/-- selectorが指定定数に等しいときtargetを反転する全dirty stage。 -/
def xorSelectorEqualsConstant
    {ancillaQubits systemQubits : Nat}
    (selector scratch : List (Wire ancillaQubits systemQubits))
    (constant : Nat) (target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  TotalReversibleStage.boolMultiControlledX
    (selectorConstantControls selector constant) scratch target

/-- controlが1のときsource wordをtarget wordへXORする全dirty stage。 -/
def controlledXorCopy
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  TotalReversibleStage.sequence <| (source.zip target).map fun pair =>
    TotalReversibleStage.safeXorDoublyControlled control pair.1 pair.2

/-- 指定bit位置以降のNat定数をcontrol付きでtargetへXORする。 -/
def controlledXorConstantAux
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (constant start : Nat) :
    List (Wire ancillaQubits systemQubits) →
      TotalReversibleStage ancillaQubits systemQubits
  | [] => .identity
  | target :: targets =>
      .seq
        (if constant.testBit start then
          TotalReversibleStage.safeXorControlled control target
        else .identity)
        (controlledXorConstantAux control constant (start + 1) targets)

/-- controlが1のときNat定数をlittle-endian targetへXORする。 -/
def controlledXorConstant
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (target : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    TotalReversibleStage ancillaQubits systemQubits :=
  controlledXorConstantAux control constant 0 target

end OracleTotalProgram

end ProbabilityGeneratorQProof
