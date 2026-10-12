import QLean.Generator.Analysis.OraclePersistentTotalStage
import QLean.Generator.Analysis.OracleTotalPrograms

/-!
# column/row diagonal branch の全 dirty 状態上の段階
-/

namespace ProbabilityGeneratorQProof

namespace OracleDiagonalTotalProgram

/-- column selector の全 wire 列。 -/
def columnSelectorWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map fun index =>
    (QLayout.canonical p).columnSelector.ancillaWire index

/-- row selector の全 wire 列。 -/
def rowSelectorWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map fun index =>
    (QLayout.canonical p).rowSelector.ancillaWire index

/-- row output の全 wire 列。 -/
def rowOutputWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map fun index =>
    (QLayout.canonical p).rowOutput.ancillaWire index

/-- selector output の全 wire 列。 -/
def selectorOutputWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map fun index =>
    (QLayout.canonical p).selectorOutput.ancillaWire index

/-- oracle work 内の幅 1 の slice が指す wire。 -/
def singletonWire (p : QParameters) (slice : RegisterSlice p.oracleWorkWidth 1) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice slice).ancillaWire 0

/-- selector 一致 flag。 -/
def selectedWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  singletonWire p (OracleWorkLayout.canonical p).selected

/-- branch 受理 flag。 -/
def branchWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  singletonWire p (OracleWorkLayout.canonical p).branch

/-- 指定 slot の present flag。 -/
def presentWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).present).ancillaWire slot

/-- decoder の AND scratch 列。 -/
def andScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  DecoderTotalProgram.andScratchWires p

/-- key signal wire。 -/
def keySignalWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).keySignal.ancillaWire 0

/-- negative amplitude wire。 -/
def negativeWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).negative.ancillaWire 0

/-- active amplitude wire。 -/
def activeWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).active.ancillaWire 0

/-- column 側の一つの diagonal branch。 -/
def columnDiagonal (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let selectorValue := 6 * slot.val + copy.val
  let computeSelector := OracleTotalProgram.xorSelectorEqualsConstant
    (columnSelectorWires p) (andScratchWires p) selectorValue (selectedWire p)
  let computeBranch := TotalReversibleStage.positiveMultiControlledX
    [DecoderTotalProgram.legalWire p, selectedWire p, presentWireAt p slot]
    (andScratchWires p) (branchWire p)
  let compute := .seq computeSelector computeBranch
  let use := .seq (OracleTotalProgram.controlledXorCopy (branchWire p)
      (OraclePersistentTotalProgram.columnKeyWires p) (rowOutputWires p)) <|
    .seq (OracleTotalProgram.controlledXorConstant (branchWire p)
      (selectorOutputWires p) selectorValue) <|
    .seq (TotalReversibleStage.safeXorControlled (branchWire p) (negativeWire p)) <|
      TotalReversibleStage.safeXorControlled (branchWire p) (activeWire p)
  TotalReversibleStage.computeUseUncompute compute use

/-- row 側の一つの diagonal branch。 -/
def rowDiagonal (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let selectorValue := 6 * slot.val + copy.val
  let computeSelector := OracleTotalProgram.xorSelectorEqualsConstant
    (rowSelectorWires p) (andScratchWires p) selectorValue (selectedWire p)
  let computeBranch := TotalReversibleStage.positiveMultiControlledX
    [DecoderTotalProgram.legalWire p, selectedWire p, presentWireAt p slot]
    (andScratchWires p) (branchWire p)
  let compute := .seq computeSelector computeBranch
  let use := .seq (OracleTotalProgram.controlledXorCopy (branchWire p)
      (OraclePersistentTotalProgram.systemWires p)
      (OraclePersistentTotalProgram.columnKeyWires p)) <|
    .seq (OracleTotalProgram.controlledXorConstant (branchWire p)
      (columnSelectorWires p) selectorValue) <|
      TotalReversibleStage.safeXorControlled (branchWire p) (keySignalWire p)
  TotalReversibleStage.computeUseUncompute compute use

end OracleDiagonalTotalProgram

end ProbabilityGeneratorQProof
