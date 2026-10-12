import QLean.Generator.Analysis.OracleDecoderTotalStage
import QLean.Generator.Implementation.TotalReversibleProgramsCompiler
import QLean.Generator.Implementation.QDecoderCircuit

/-!
# compact decoder全dirty stageのcompiler一致
-/

namespace ProbabilityGeneratorQProof

namespace DecoderTotalProgram

/-- pure wire配置は既存decoder配置と一致する。 -/
theorem degreeWires_eq (p : QParameters) : degreeWires p = oracleDegreeWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem legalWire_eq (p : QParameters) : legalWire p = oracleLegalWire p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem andWorkWires_eq (p : QParameters) : andWorkWires p = oracleAndWorkWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem compareWorkWires_eq (p : QParameters) :
    compareWorkWires p = oracleCompareWorkWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem suffixWires_eq (p : QParameters) : suffixWires p = decoderSuffixWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem lessWires_eq (p : QParameters) : lessWires p = decoderLessWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem needWires_eq (p : QParameters) : needWires p = decoderNeedWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem goodWires_eq (p : QParameters) : goodWires p = decoderGoodWires p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem degreeValidWire_eq (p : QParameters) :
    degreeValidWire p = decoderDegreeValidWire p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem legalTemporaryWire_eq (p : QParameters) :
    legalTemporaryWire p = decoderLegalTemporaryWire p := rfl
/-- pure wire配置は既存decoder配置と一致する。 -/
theorem andScratchWires_eq (p : QParameters) :
    andScratchWires p = decoderAndScratchWires p := rfl

/-- OR-XOR stageのcompilerは既存三gate回路と一致する。 -/
theorem compile_reversibleOrXor {ancillaQubits systemQubits : Nat}
    (left right target : Wire ancillaQubits systemQubits) :
    (reversibleOrXor left right target).compile =
      ProbabilityGeneratorQProof.reversibleOrXor left right target := by
  simp [reversibleOrXor, ProbabilityGeneratorQProof.reversibleOrXor,
    TotalReversibleStage.compile,
    TotalReversibleStage.compile_safeXorControlled,
    TotalReversibleStage.compile_safeXorDoublyControlled]

/-- suffix OR stageのcompilerは既存再帰回路と一致する。 -/
theorem compile_suffixOr {ancillaQubits systemQubits : Nat}
    (input suffix : List (Wire ancillaQubits systemQubits)) :
    (suffixOr input suffix).compile =
      ProbabilityGeneratorQProof.suffixOrCircuit input suffix := by
  induction input, suffix using suffixOr.induct with
  | case1 => rfl
  | case2 input =>
      simp [suffixOr, ProbabilityGeneratorQProof.suffixOrCircuit,
        TotalReversibleStage.compile]
  | case3 inputLast suffixLast =>
      exact TotalReversibleStage.compile_safeXorControlled inputLast suffixLast
  | case4 inputHead inputNext inputTail suffixHead suffixNext suffixTail inductionHypothesis =>
      simp [suffixOr, ProbabilityGeneratorQProof.suffixOrCircuit,
        TotalReversibleStage.compile, inductionHypothesis, compile_reversibleOrXor]
  | case5 input suffix =>
      simp [suffixOr, ProbabilityGeneratorQProof.suffixOrCircuit,
        TotalReversibleStage.compile, *]

/-- 一境界stageのcompilerは既存境界回路と一致する。 -/
theorem compile_degreeBoundary {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits) :
    (degreeBoundary wordWidth input suffix degree flag).compile =
      ProbabilityGeneratorQProof.degreeBoundaryCircuit
        wordWidth input suffix degree flag := by
  simp only [degreeBoundary, ProbabilityGeneratorQProof.degreeBoundaryCircuit]
  generalize input[wordWidth * (degree + 1)]? = inputBoundary
  cases inputBoundary with
  | none => rfl
  | some delimiter =>
      generalize suffix[wordWidth * (degree + 1) + 1]? = laterBoundary
      cases laterBoundary with
      | none =>
          exact TotalReversibleStage.compile_safeXorControlled delimiter flag
      | some laterNonzero =>
          simp [TotalReversibleStage.compile,
            TotalReversibleInstruction.toReversibleGate,
            TotalReversibleStage.compile_safeXorDoublyControlled]

/-- 境界列stageのcompilerは既存再帰回路と一致する。 -/
theorem compile_degreeBoundarySequence {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flags : List (Wire ancillaQubits systemQubits)) :
    (degreeBoundarySequence wordWidth input suffix degree flags).compile =
      ProbabilityGeneratorQProof.degreeBoundarySequence
        wordWidth input suffix degree flags := by
  induction flags generalizing degree with
  | nil => rfl
  | cons flag flags inductionHypothesis =>
      simp [degreeBoundarySequence,
        ProbabilityGeneratorQProof.degreeBoundarySequence,
        TotalReversibleStage.compile, compile_degreeBoundary,
        inductionHypothesis]

/-- degree one-hot stageのcompilerは既存compute--use--uncompute回路と一致する。 -/
theorem compile_xorDelimiterDegreeOneHotIntoTargets
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix flags : List (Wire ancillaQubits systemQubits)) :
    (xorDelimiterDegreeOneHotIntoTargets wordWidth input suffix flags).compile =
      ProbabilityGeneratorQProof.xorDelimiterDegreeOneHotIntoTargetsCircuit
        wordWidth input suffix flags := by
  rw [xorDelimiterDegreeOneHotIntoTargets,
    ProbabilityGeneratorQProof.xorDelimiterDegreeOneHotIntoTargetsCircuit]
  rw [TotalReversibleStage.compile_computeUseUncompute]
  rw [compile_suffixOr, compile_degreeBoundarySequence]

/-- pure word分割は既存補助関数と一致する。 -/
theorem splitWords_eq {ancillaQubits systemQubits : Nat}
    (wordWidth wordCount : Nat)
    (input : List (Wire ancillaQubits systemQubits)) :
    splitWords wordWidth wordCount input =
      ProbabilityGeneratorQProof.splitSystemWords wordWidth wordCount input := rfl

/-- slot presence再帰stageのcompilerは既存再帰回路と一致する。 -/
theorem compile_xorDegreeSuffixParityIntoSlotPresence
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (presentFlags : List (Wire ancillaQubits systemQubits)) :
    (xorDegreeSuffixParityIntoSlotPresence degreeFlags slot presentFlags).compile =
      ProbabilityGeneratorQProof.xorDegreeSuffixParityIntoSlotPresenceCircuit
        degreeFlags slot presentFlags := by
  induction presentFlags generalizing slot with
  | nil => rfl
  | cons presentFlag presentFlags inductionHypothesis =>
      rw [xorDegreeSuffixParityIntoSlotPresence,
        ProbabilityGeneratorQProof.xorDegreeSuffixParityIntoSlotPresenceCircuit]
      rw [TotalReversibleStage.compile]
      rw [TotalReversibleStage.compile_sequence_map
        (degreeFlags.drop slot)
        (fun degreeFlag => TotalReversibleStage.safeXorControlled
          degreeFlag presentFlag)
        (fun degreeFlag => ReversibleCircuit.safeCnot degreeFlag presentFlag)
        (fun degreeFlag =>
          TotalReversibleStage.compile_safeXorControlled degreeFlag presentFlag)]
      rw [inductionHypothesis]

/-- slot presence stageのcompilerは既存回路と一致する。 -/
theorem compile_slotPresence {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits)) :
    (slotPresence degreeFlags presentFlags).compile =
      ProbabilityGeneratorQProof.slotPresenceCircuit degreeFlags presentFlags :=
  compile_xorDegreeSuffixParityIntoSlotPresence degreeFlags 0 presentFlags

/-- 一比較step stageのcompilerは既存step回路と一致する。 -/
theorem compile_comparisonStep {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (left right : List (Wire ancillaQubits systemQubits))
    (less need good : Wire ancillaQubits systemQubits) :
    (comparisonStep degreeFlags compareWork andScratch slot
        left right less need good).compile =
      ProbabilityGeneratorQProof.decoderComparisonStep
        degreeFlags compareWork andScratch slot left right less need good := by
  have needEqual :
      (TotalReversibleStage.sequence <|
        (degreeFlags.drop (slot + 1)).map fun degreeFlag =>
          TotalReversibleStage.safeXorControlled degreeFlag need).compile =
      VerifiedCircuitCore.Circuit.sequence
        ((degreeFlags.drop (slot + 1)).map fun degreeFlag =>
          ReversibleCircuit.safeCnot degreeFlag need) :=
    TotalReversibleStage.compile_sequence_map
      (degreeFlags.drop (slot + 1))
      (fun degreeFlag => TotalReversibleStage.safeXorControlled degreeFlag need)
      (fun degreeFlag => ReversibleCircuit.safeCnot degreeFlag need)
      (fun degreeFlag =>
        TotalReversibleStage.compile_safeXorControlled degreeFlag need)
  have needEqualDropped := needEqual
  rw [List.map_drop] at needEqualDropped
  simp [comparisonStep, ProbabilityGeneratorQProof.decoderComparisonStep,
    TotalReversibleStage.compile,
    TotalReversibleStage.compile_xorLessThanIntoTarget,
    TotalReversibleStage.compile_safeXorDoublyControlled,
    TotalReversibleInstruction.toReversibleGate, needEqualDropped]

/-- 比較列stageのcompilerは既存再帰回路と一致する。 -/
theorem compile_comparisonSequence {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits)) :
    (comparisonSequence degreeFlags compareWork andScratch slot
        words lessFlags needFlags goodFlags).compile =
      ProbabilityGeneratorQProof.decoderComparisonSequence
        degreeFlags compareWork andScratch slot words lessFlags needFlags goodFlags := by
  induction words generalizing slot lessFlags needFlags goodFlags with
  | nil => rfl
  | cons left rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons right words =>
          cases lessFlags with
          | nil => rfl
          | cons less lessFlags =>
              cases needFlags with
              | nil => rfl
              | cons need needFlags =>
                  cases goodFlags with
                  | nil => rfl
                  | cons good goodFlags =>
                      simp [comparisonSequence,
                        ProbabilityGeneratorQProof.decoderComparisonSequence,
                        TotalReversibleStage.compile, compile_comparisonStep,
                        inductionHypothesis]

/-- degree-valid stageのcompilerは既存finite sequenceと一致する。 -/
theorem compile_degreeValid {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits))
    (degreeValidWire : Wire ancillaQubits systemQubits) :
    (degreeValid degreeFlags degreeValidWire).compile =
      ProbabilityGeneratorQProof.decoderDegreeValidCircuit
        degreeFlags degreeValidWire := by
  rw [degreeValid, ProbabilityGeneratorQProof.decoderDegreeValidCircuit]
  exact TotalReversibleStage.compile_sequence_map degreeFlags
    (fun flag => TotalReversibleStage.safeXorControlled flag degreeValidWire)
    (fun flag => ReversibleCircuit.safeCnot flag degreeValidWire)
    (fun flag =>
      TotalReversibleStage.compile_safeXorControlled flag degreeValidWire)

/-- legality compute stageのcompilerは既存compute回路と一致する。 -/
theorem compile_legalityCompute {ancillaQubits systemQubits : Nat}
    (words : List (List (Wire ancillaQubits systemQubits)))
    (degreeFlags lessFlags needFlags goodFlags compareWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (degreeValidWire legalTemporary : Wire ancillaQubits systemQubits) :
    (legalityCompute words degreeFlags lessFlags needFlags goodFlags
        compareWork andScratch degreeValidWire legalTemporary).compile =
      ProbabilityGeneratorQProof.decoderLegalityCompute words degreeFlags
        lessFlags needFlags goodFlags compareWork andScratch
        degreeValidWire legalTemporary := by
  simp [legalityCompute, ProbabilityGeneratorQProof.decoderLegalityCompute,
    TotalReversibleStage.compile, compile_degreeValid,
    compile_comparisonSequence,
    TotalReversibleStage.compile_positiveMultiControlledX]

/-- compact decoder純粋stageのcompilerは既存正本可逆回路と一致する。 -/
theorem compile_xorDelimiterLegalityAndDegreeOneHotIntoTargets
    (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargets p input).compile =
      ProbabilityGeneratorQProof.xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit
        p input := by
  rw [xorDelimiterLegalityAndDegreeOneHotIntoTargets,
    ProbabilityGeneratorQProof.xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit]
  rw [degreeWires_eq, legalWire_eq, compareWorkWires_eq, suffixWires_eq,
    lessWires_eq, needWires_eq, goodWires_eq, degreeValidWire_eq,
    legalTemporaryWire_eq, andScratchWires_eq, splitWords_eq]
  rw [TotalReversibleStage.compile]
  rw [compile_xorDelimiterDegreeOneHotIntoTargets]
  rw [TotalReversibleStage.compile_computeUseUncompute]
  rw [compile_legalityCompute]
  rw [TotalReversibleStage.compile_safeXorControlled]

end DecoderTotalProgram

end ProbabilityGeneratorQProof
