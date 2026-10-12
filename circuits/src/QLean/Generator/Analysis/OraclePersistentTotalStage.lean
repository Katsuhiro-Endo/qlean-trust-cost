import QLean.Generator.Analysis.OracleDecoderTotalStage

/-!
# oracle persistent computeの全dirty純粋stage
-/

namespace ProbabilityGeneratorQProof

namespace OraclePersistentTotalProgram

/-- system register全wire列。 -/
def systemWires (p : QParameters) : List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map fun index => QLayout.systemWire p index

/-- column key全wire列。 -/
def columnKeyWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map fun index =>
    (QLayout.canonical p).columnKey.ancillaWire index

/-- oracle present flag列。 -/
def presentWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.presentWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).present).ancillaWire index

/-- 幅1のoracle sliceをwireへ読む。 -/
def singletonWire (p : QParameters) (slice : RegisterSlice p.oracleWorkWidth 1) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice slice).ancillaWire 0

/-- degree境界条件flag。 -/
def degreeConditionWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  singletonWire p (OracleWorkLayout.canonical p).degreeCondition

/-- persistent scope中の定数1 wire。 -/
def oneWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  singletonWire p (OracleWorkLayout.canonical p).constantOne

/-- decoder・presence・degree parity・oneを順に計算するpersistent stage。 -/
def persistent (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) (rowMode : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let degreeFlags := DecoderTotalProgram.degreeWires p
  let degreeConditionSources :=
    if rowMode then degreeFlags.take (p.K - 1) else degreeFlags.drop 1
  .seq (DecoderTotalProgram.xorDelimiterLegalityAndDegreeOneHotIntoTargets p input) <|
    .seq (DecoderTotalProgram.slotPresence degreeFlags (presentWires p)) <|
      .seq (TotalReversibleStage.sequence <|
        degreeConditionSources.map fun flag =>
          TotalReversibleStage.safeXorControlled flag (degreeConditionWire p)) <|
        .instruction (.xorOne (oneWire p))

/-- column oracle用persistent stage。 -/
def columnPersistent (p : QParameters) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  persistent p (columnKeyWires p) false

/-- row oracle用persistent stage。 -/
def rowPersistent (p : QParameters) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  persistent p (systemWires p) true

end OraclePersistentTotalProgram

end ProbabilityGeneratorQProof
