import QLean.Generator.Analysis.ProbabilityGeneratorFullOperator
import QLean.Generator.Implementation.ComponentSemantics
import QLean.Generator.Implementation.PrimitiveCoreSemanticsAdapter
import QLean.Generator.Implementation.QTopLevelCorrectness
import QLean.Generator.Implementation.ReversibleLogicSharedCoreAdapter

/-!
# top-level COPYの共有core adapter

canonical system registerとcolumn-key registerの検証済みlayoutを作り、凍結Q primitive
ASTを共有register-XOR-copy componentの独立targetへ結ぶ。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- system registerからcolumn-key registerへのcanonicalな検証済みlayout。 -/
def systemIntoColumnKeyValidatedRegisterXorCopyLayout (p : QParameters) :
    ValidatedRegisterXorCopyLayout
      p.ancillaWidth p.systemWidth p.systemWidth where
  source := {
    wire := Wire.system
    injective := by
      intro left right equal
      exact Wire.system.inj equal
  }
  target := {
    wire := columnKeyWire p
    injective := columnKeyWire_injective p
  }
  disjoint := by
    intro sourceIndex targetIndex equal
    cases equal

/-- implementation layoutをcoreへ移すとpure側のcanonical specになる。 -/
theorem systemIntoColumnKeyValidatedLayout_toCore
    (p : QParameters) :
    (systemIntoColumnKeyValidatedRegisterXorCopyLayout p).toCore =
      systemIntoColumnKeyCoreRegisterXorCopySpec p := by
  rfl

/-- Q primitive COPYをcoreへ写したASTは、検証済みreversible compiler ASTと一致する。 -/
theorem xorSystemIntoColumnKeyPrimitiveCircuit_map_toCore_eq_frozenCompiler
    (p : QParameters) :
    (xorSystemIntoColumnKeyPrimitiveCircuit p).mapGates
        PrimitiveGate.toCanonicalCore =
      compileReversibleCircuitToCanonicalCore
        (xorSystemIntoColumnKeyReversibleCircuit p) := by
  rw [xorSystemIntoColumnKeyPrimitiveCircuit_eq_reversible]
  unfold ReversibleCircuit.toPrimitive Circuit.map
  rw [VerifiedCircuitCore.Circuit.mapGates_mapGates]
  rw [primitiveGateToCanonicalCore_comp_toPrimitive]
  rfl

/--
共有copy childの`correct`を、凍結Q primitive ASTとJointBasisへ移したExact component。
-/
def xorSystemIntoColumnKeySharedCoreExactOperatorComponent
    (p : QParameters) :
    ExactOperatorComponent
      (primitiveGateOperator :
        PrimitiveGate p.ancillaWidth p.systemWidth →
          Operator (JointBasis p.ancillaWidth p.systemWidth)) where
  circuit := xorSystemIntoColumnKeyPrimitiveCircuit p
  target := reindexCanonicalCoreOperatorToJoint
    (VerifiedCircuitCore.registerXorCopyPureOperator
      (systemIntoColumnKeyCoreRegisterXorCopySpec p))
  correct := by
    let layout := systemIntoColumnKeyValidatedRegisterXorCopyLayout p
    let child := validatedXorSourceRegisterIntoTargetFrozenCompilerExactComponent
      internalZeroSymbolEnvironment layout
    have compiledCorrect :
        VerifiedCircuitCore.Circuit.denote
            (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
              (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment)
            ((xorSystemIntoColumnKeyPrimitiveCircuit p).mapGates
              PrimitiveGate.toCanonicalCore) =
          child.target := by
      rw [xorSystemIntoColumnKeyPrimitiveCircuit_map_toCore_eq_frozenCompiler]
      exact child.correct
    have reindexedCorrect :
        reindexJointOperatorToCanonicalCore
            (VerifiedCircuitCore.Circuit.denote primitiveGateOperator
              (xorSystemIntoColumnKeyPrimitiveCircuit p)) =
          child.target := by
      rw [← compileCircuitToCanonicalCore_denote]
      exact compiledCorrect
    calc
      VerifiedCircuitCore.Circuit.denote primitiveGateOperator
          (xorSystemIntoColumnKeyPrimitiveCircuit p) =
        reindexCanonicalCoreOperatorToJoint
          (reindexJointOperatorToCanonicalCore
            (VerifiedCircuitCore.Circuit.denote primitiveGateOperator
              (xorSystemIntoColumnKeyPrimitiveCircuit p))) :=
        (reindexCanonicalCoreOperatorToJoint_joint _).symm
      _ = reindexCanonicalCoreOperatorToJoint child.target :=
        congrArg reindexCanonicalCoreOperatorToJoint reindexedCorrect
      _ = reindexCanonicalCoreOperatorToJoint
          (VerifiedCircuitCore.registerXorCopyPureOperator
            (systemIntoColumnKeyCoreRegisterXorCopySpec p)) := by
        congr 1

end

end ProbabilityGeneratorQProof
