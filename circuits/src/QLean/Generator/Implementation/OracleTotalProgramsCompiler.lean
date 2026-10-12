import QLean.Generator.Analysis.OracleTotalPrograms
import QLean.Generator.Implementation.TotalReversibleProgramsCompiler
import QLean.Generator.Implementation.QOracleCircuit

/-!
# oracle局所writer stageのcompiler一致
-/

namespace ProbabilityGeneratorQProof

namespace OracleTotalProgram

/-- 純粋selector制御列の内部再帰は既存constructorと一致する。 -/
theorem selectorConstantControlsAux_eq
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat)
    (selector : List (Wire ancillaQubits systemQubits)) :
    selectorConstantControlsAux constant start selector =
      ProbabilityGeneratorQProof.selectorConstantControlsAux
        constant start selector := by
  induction selector generalizing start with
  | nil => rfl
  | cons wire selector inductionHypothesis =>
      simp [selectorConstantControlsAux,
        ProbabilityGeneratorQProof.selectorConstantControlsAux,
        inductionHypothesis]

/-- 純粋selector制御列は既存constructorの制御列と一致する。 -/
theorem selectorConstantControls_eq
    {ancillaQubits systemQubits : Nat}
    (selector : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    selectorConstantControls selector constant =
      ProbabilityGeneratorQProof.selectorConstantControls selector constant :=
  selectorConstantControlsAux_eq constant 0 selector

/-- selector定数比較stageのcompilerは既存selector回路と一致する。 -/
theorem compile_xorSelectorEqualsConstant
    {ancillaQubits systemQubits : Nat}
    (selector scratch : List (Wire ancillaQubits systemQubits))
    (constant : Nat) (target : Wire ancillaQubits systemQubits) :
    (xorSelectorEqualsConstant selector scratch constant target).compile =
      ProbabilityGeneratorQProof.selectorEqualsConstant
        selector scratch constant target := by
  rw [xorSelectorEqualsConstant,
    TotalReversibleStage.compile_boolMultiControlledX]
  rw [selectorConstantControls_eq]
  rfl

/-- 制御copy stageのcompilerは既存制御copy回路と一致する。 -/
theorem compile_controlledXorCopy
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits)) :
    (controlledXorCopy control source target).compile =
      ProbabilityGeneratorQProof.controlledXorCopy control source target := by
  rw [controlledXorCopy, TotalReversibleStage.compile_sequence]
  rw [ProbabilityGeneratorQProof.controlledXorCopy]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro pair _
  exact TotalReversibleStage.compile_safeXorDoublyControlled
    control pair.1 pair.2

/-- 制御定数XORの再帰stageは既存再帰回路と一致する。 -/
theorem compile_controlledXorConstantAux
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (constant start : Nat)
    (targets : List (Wire ancillaQubits systemQubits)) :
    (controlledXorConstantAux control constant start targets).compile =
      ProbabilityGeneratorQProof.controlledXorConstantAux
        control constant start targets := by
  induction targets generalizing start with
  | nil => rfl
  | cons target targets inductionHypothesis =>
      by_cases bit : constant.testBit start
      · simp [controlledXorConstantAux,
          ProbabilityGeneratorQProof.controlledXorConstantAux, bit,
          TotalReversibleStage.compile,
          TotalReversibleStage.compile_safeXorControlled,
          inductionHypothesis]
      · simp [controlledXorConstantAux,
          ProbabilityGeneratorQProof.controlledXorConstantAux, bit,
          TotalReversibleStage.compile, inductionHypothesis]

/-- 制御定数XOR stageのcompilerは既存回路と一致する。 -/
theorem compile_controlledXorConstant
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (target : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    (controlledXorConstant control target constant).compile =
      ProbabilityGeneratorQProof.controlledXorConstant control target constant :=
  compile_controlledXorConstantAux control constant 0 target

end OracleTotalProgram

end ProbabilityGeneratorQProof
