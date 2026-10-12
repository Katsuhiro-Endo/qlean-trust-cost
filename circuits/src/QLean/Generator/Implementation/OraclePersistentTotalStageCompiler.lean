import QLean.Generator.Analysis.OraclePersistentTotalStage
import QLean.Generator.Implementation.OracleDecoderTotalStageCompiler
import QLean.Generator.Implementation.QOracleCircuit

/-!
# oracle persistent全dirty stageのcompiler一致
-/

namespace ProbabilityGeneratorQProof

namespace OraclePersistentTotalProgram

/-- pure wire配置は既存oracle配置と一致する。 -/
theorem systemWires_eq (p : QParameters) :
    systemWires p = ProbabilityGeneratorQProof.systemWires p := rfl
/-- pure wire配置は既存oracle配置と一致する。 -/
theorem columnKeyWires_eq (p : QParameters) :
    columnKeyWires p = ProbabilityGeneratorQProof.columnKeyWires p := rfl
/-- pure wire配置は既存oracle配置と一致する。 -/
theorem presentWires_eq (p : QParameters) :
    presentWires p = ProbabilityGeneratorQProof.oraclePresentWires p := rfl
/-- pure wire配置は既存oracle配置と一致する。 -/
theorem degreeConditionWire_eq (p : QParameters) :
    degreeConditionWire p = ProbabilityGeneratorQProof.oracleDegreeConditionWire p := rfl
/-- pure wire配置は既存oracle配置と一致する。 -/
theorem oneWire_eq (p : QParameters) :
    oneWire p = ProbabilityGeneratorQProof.oracleOneWire p := rfl

/-- flag列を一つのtargetへXORするstage列は既存CNOT列へcompileされる。 -/
theorem compile_xorFlagsIntoTarget
    {ancillaQubits systemQubits : Nat}
    (flags : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    (TotalReversibleStage.sequence <| flags.map fun flag =>
      TotalReversibleStage.safeXorControlled flag target).compile =
      VerifiedCircuitCore.Circuit.sequence
        (flags.map fun flag => ReversibleCircuit.safeCnot flag target) :=
  TotalReversibleStage.compile_sequence_map flags
    (fun flag => TotalReversibleStage.safeXorControlled flag target)
    (fun flag => ReversibleCircuit.safeCnot flag target)
    (fun flag => TotalReversibleStage.compile_safeXorControlled flag target)

/-- persistent pure stageのcompilerは既存persistent回路と一致する。 -/
theorem compile_persistent (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) (rowMode : Bool) :
    (persistent p input rowMode).compile =
      ProbabilityGeneratorQProof.computeSharedDecoderPresenceParityAndOneFlagsCircuit
        p input rowMode := by
  simp [persistent,
    ProbabilityGeneratorQProof.computeSharedDecoderPresenceParityAndOneFlagsCircuit,
    DecoderTotalProgram.degreeWires_eq, presentWires_eq,
    degreeConditionWire_eq, oneWire_eq,
    TotalReversibleStage.compile,
    DecoderTotalProgram.compile_xorDelimiterLegalityAndDegreeOneHotIntoTargets,
    DecoderTotalProgram.compile_slotPresence,
    TotalReversibleInstruction.toReversibleGate, compile_xorFlagsIntoTarget]

/-- column persistent stageのcompilerは既存column persistent回路と一致する。 -/
theorem compile_columnPersistent (p : QParameters) :
    (columnPersistent p).compile =
      ProbabilityGeneratorQProof.computeSharedDecoderPresenceParityAndOneFlagsCircuit
        p (ProbabilityGeneratorQProof.columnKeyWires p) false := by
  rw [columnPersistent, compile_persistent, columnKeyWires_eq]

/-- row persistent stageのcompilerは既存row persistent回路と一致する。 -/
theorem compile_rowPersistent (p : QParameters) :
    (rowPersistent p).compile =
      ProbabilityGeneratorQProof.computeSharedDecoderPresenceParityAndOneFlagsCircuit
        p (ProbabilityGeneratorQProof.systemWires p) true := by
  rw [rowPersistent, compile_persistent, systemWires_eq]

/-- column persistentを全入力基底置換へ結ぶcomponent。 -/
def columnPersistentPermutationComponent (p : QParameters) :=
  (columnPersistent p).permutationComponent

/-- row persistentを全入力基底置換へ結ぶcomponent。 -/
def rowPersistentPermutationComponent (p : QParameters) :=
  (rowPersistent p).permutationComponent

end OraclePersistentTotalProgram

end ProbabilityGeneratorQProof
