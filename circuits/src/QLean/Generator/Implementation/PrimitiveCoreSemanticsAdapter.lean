import QLean.Generator.Implementation.CoreCircuitEmbeddingSemantics
import QLean.Circuits.Foundation.Combinators
import QLean.Generator.Implementation.SparseCircuitSemantics
import QLean.Generator.Implementation.TwoWireSemantics
import QLean.Circuits.Foundation.PrimitiveGateProofs

/-!
# Q primitive回路の共有core意味論adapter

Q固有の所属付き基底と標準Qubit基底の付け替えが、基本ゲートおよび
回路の合成意味論を保存することを証明する。九段Q回路やblock encodingは参照しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Qには自由なsymbol角度がないため、共有core評価環境を零へ固定する。 -/
def internalZeroSymbolEnvironment : String → ℝ := fun _ => 0

/-- 所属付きQ基底上の作用素を標準数値Qubit基底へ付け替える。 -/
def reindexJointOperatorToCanonicalCore
    {ancillaQubits systemQubits : Nat}
    (operator : Operator (JointBasis ancillaQubits systemQubits)) :
    VerifiedCircuitCore.Operator
      (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits)) :=
  Matrix.reindex (jointBasisCoreEquiv ancillaQubits systemQubits)
    (jointBasisCoreEquiv ancillaQubits systemQubits) operator

/-- 標準Qubit基底上の作用素を所属付きQ基底へ戻す乗法準同型。 -/
def reindexCanonicalCoreOperatorToJoint
    {ancillaQubits systemQubits : Nat} :
    VerifiedCircuitCore.Operator
        (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits)) →*
      Operator (JointBasis ancillaQubits systemQubits) :=
  (Matrix.reindexRingEquiv ℂ
    (jointBasisCoreEquiv ancillaQubits systemQubits).symm).toMonoidHom

/-- 標準Qubit基底上の状態を所属付きQ基底へ戻す。 -/
def reindexCanonicalCoreStateToJoint
    {ancillaQubits systemQubits : Nat}
    (state : VerifiedCircuitCore.State
      (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits))) :
    State (JointBasis ancillaQubits systemQubits) :=
  fun basis => state (jointBasisToCore basis)

/-- 作用素と状態を同じ基底同値で戻す操作は行列作用と可換である。 -/
theorem applyOperator_reindexCanonicalCoreToJoint
    {ancillaQubits systemQubits : Nat}
    (operator : VerifiedCircuitCore.Operator
      (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits)))
    (state : VerifiedCircuitCore.State
      (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits))) :
    applyOperator (reindexCanonicalCoreOperatorToJoint operator)
        (reindexCanonicalCoreStateToJoint state) =
      reindexCanonicalCoreStateToJoint (applyOperator operator state) := by
  funext output
  unfold applyOperator VerifiedCircuitCore.applyOperator Matrix.mulVec dotProduct
    reindexCanonicalCoreStateToJoint reindexCanonicalCoreOperatorToJoint
  change
    (∑ input : JointBasis ancillaQubits systemQubits,
      operator (jointBasisToCore output) (jointBasisToCore input) *
        state (jointBasisToCore input)) =
      ∑ input : VerifiedCircuitCore.QubitBasis
          (ancillaQubits + systemQubits),
        operator (jointBasisToCore output) input * state input
  exact Fintype.sum_equiv
    (jointBasisCoreEquiv ancillaQubits systemQubits)
    (fun input =>
      operator (jointBasisToCore output) (jointBasisToCore input) *
        state (jointBasisToCore input))
    (fun input => operator (jointBasisToCore output) input * state input)
    (fun input => by rfl)

/-- Q作用素を標準基底へ移してから戻すと元へ戻る。 -/
@[simp] theorem reindexCanonicalCoreOperatorToJoint_joint
    {ancillaQubits systemQubits : Nat}
    (operator : Operator (JointBasis ancillaQubits systemQubits)) :
    reindexCanonicalCoreOperatorToJoint
        (reindexJointOperatorToCanonicalCore operator) = operator := by
  ext output input
  simp [reindexCanonicalCoreOperatorToJoint,
    reindexJointOperatorToCanonicalCore, Matrix.reindex_apply]

/-- Qと共有coreで用いる局所X行列は同一である。 -/
theorem xMatrix_eq_coreLocalX : xMatrix = VerifiedCircuitCore.localX := by
  rfl

/-- Qと共有coreで用いる局所Ry行列は同一である。 -/
theorem ryMatrix_eq_coreLocalRy (angle : ℝ) :
    ryMatrix angle = VerifiedCircuitCore.localRy angle := by
  rfl

/-- 標準Qubit基底を所属付きQ基底へ戻したときのwire値。 -/
@[simp] theorem coreBasisToJoint_apply
    {ancillaQubits systemQubits : Nat}
    (basis : VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits))
    (wire : Wire ancillaQubits systemQubits) :
    coreBasisToJoint basis wire = basis (wireToCanonicalFin wire) := by
  rfl

/-- 標準基底上の一wire一致条件を所属付きQ基底へ移す。 -/
theorem agreesExcept_coreBasisToJoint_iff
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (output input : VerifiedCircuitCore.QubitBasis
      (ancillaQubits + systemQubits)) :
    VerifiedCircuitCore.agreesExcept (wireToCanonicalFin target) output input ↔
      SameOutside target (coreBasisToJoint output) (coreBasisToJoint input) := by
  have result := agreesExcept_jointBasisToCore_iff target
    (coreBasisToJoint output) (coreBasisToJoint input)
  have outputRoundTrip : jointBasisToCore (coreBasisToJoint output) = output :=
    (jointBasisCoreEquiv ancillaQubits systemQubits).apply_symm_apply output
  have inputRoundTrip : jointBasisToCore (coreBasisToJoint input) = input :=
    (jointBasisCoreEquiv ancillaQubits systemQubits).apply_symm_apply input
  rw [outputRoundTrip, inputRoundTrip] at result
  exact result

/-- CNOTのpure基底作用は標準基底付け替えと可換である。 -/
theorem coreBasisToJoint_cnotBasisAction
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (input : VerifiedCircuitCore.QubitBasis
      (ancillaQubits + systemQubits)) :
    coreBasisToJoint
        (VerifiedCircuitCore.cnotBasisAction
          (wireToCanonicalFin control) (wireToCanonicalFin target) input) =
      cnotBasisAction control target (coreBasisToJoint input) := by
  funext wire
  by_cases enabled : input (wireToCanonicalFin control)
  · by_cases isTarget : wire = target
    · subst wire
      simp [VerifiedCircuitCore.cnotBasisAction,
        VerifiedCircuitCore.xorWire, cnotBasisAction, enabled]
    · have mappedDifferent : wireToCanonicalFin wire ≠ wireToCanonicalFin target :=
        fun equal => isTarget (wireToCanonicalFin_injective equal)
      simp [VerifiedCircuitCore.cnotBasisAction,
        VerifiedCircuitCore.xorWire, cnotBasisAction, enabled,
        isTarget, mappedDifferent]
  · simp [VerifiedCircuitCore.cnotBasisAction,
      VerifiedCircuitCore.xorWire, cnotBasisAction, enabled]

/-- Toffoliのpure基底作用は標準基底付け替えと可換である。 -/
theorem coreBasisToJoint_toffoliBasisAction
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (input : VerifiedCircuitCore.QubitBasis
      (ancillaQubits + systemQubits)) :
    coreBasisToJoint
        (VerifiedCircuitCore.toffoliBasisAction
          (wireToCanonicalFin control₁) (wireToCanonicalFin control₂)
          (wireToCanonicalFin target) input) =
      toffoliBasisAction control₁ control₂ target (coreBasisToJoint input) := by
  funext wire
  by_cases firstEnabled : input (wireToCanonicalFin control₁)
  · by_cases secondEnabled : input (wireToCanonicalFin control₂)
    · by_cases isTarget : wire = target
      · subst wire
        simp [VerifiedCircuitCore.toffoliBasisAction,
          VerifiedCircuitCore.xorWire, toffoliBasisAction,
          firstEnabled, secondEnabled]
      · have mappedDifferent :
            wireToCanonicalFin wire ≠ wireToCanonicalFin target :=
          fun equal => isTarget (wireToCanonicalFin_injective equal)
        simp [VerifiedCircuitCore.toffoliBasisAction,
          VerifiedCircuitCore.xorWire, toffoliBasisAction,
          firstEnabled, secondEnabled, isTarget, mappedDifferent]
    · simp [VerifiedCircuitCore.toffoliBasisAction,
        VerifiedCircuitCore.xorWire, toffoliBasisAction,
        firstEnabled, secondEnabled]
  · simp [VerifiedCircuitCore.toffoliBasisAction,
      VerifiedCircuitCore.xorWire, toffoliBasisAction, firstEnabled]

/-- Q側Toffoli置換行列の疎な計算基底要素。 -/
theorem toffoliMatrix_apply_coreAdapter
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (output input : JointBasis ancillaQubits systemQubits) :
    toffoliMatrix control₁ control₂ target controlsDifferent firstDifferent
        secondDifferent output input =
      if output = toffoliBasisAction control₁ control₂ target input then 1 else 0 := by
  let circuit : Circuit (ReversibleGate ancillaQubits systemQubits) :=
    .gate (.toffoli control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent)
  have amplitude := reversibleCircuit_basisAmplitude circuit input output
  simpa [circuit, ReversibleCircuit.toPrimitive, Circuit.map,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.denote, ReversibleGate.toPrimitive,
    primitiveGateOperator] using amplitude

/-- Q primitive gateの標準core compileは、Q作用素の基底付け替えに一致する。 -/
theorem primitiveGate_toCanonicalCore_operator
    {ancillaQubits systemQubits : Nat}
    (gate : PrimitiveGate ancillaQubits systemQubits) :
    VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment
        gate.toCanonicalCore =
      reindexJointOperatorToCanonicalCore (primitiveGateOperator gate) := by
  ext output input
  cases gate with
  | x target =>
      simp only [PrimitiveGate.toCanonicalCore,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols,
        ProbabilityGeneratorQProof.primitiveGateOperator,
        reindexJointOperatorToCanonicalCore, Matrix.reindex_apply]
      rw [VerifiedCircuitCore.embedSingleQubitOperator_apply]
      change (if VerifiedCircuitCore.agreesExcept (wireToCanonicalFin target)
          output input then
            VerifiedCircuitCore.localX (output (wireToCanonicalFin target))
              (input (wireToCanonicalFin target))
          else 0) =
        onWire target xMatrix (coreBasisToJoint output) (coreBasisToJoint input)
      rw [onWire_apply]
      by_cases agrees : VerifiedCircuitCore.agreesExcept
          (wireToCanonicalFin target) output input
      · have qAgrees := (agreesExcept_coreBasisToJoint_iff target output input).mp
          agrees
        rw [if_pos agrees, if_pos qAgrees]
        exact (congrFun (congrFun xMatrix_eq_coreLocalX
          (output (wireToCanonicalFin target)))
          (input (wireToCanonicalFin target))).symm
      · have qDiffers :
            ¬ SameOutside target (coreBasisToJoint output) (coreBasisToJoint input) :=
          fun qAgrees => agrees
            ((agreesExcept_coreBasisToJoint_iff target output input).mpr qAgrees)
        rw [if_neg agrees, if_neg qDiffers]
  | h target =>
      simp only [PrimitiveGate.toCanonicalCore,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols,
        ProbabilityGeneratorQProof.primitiveGateOperator,
        reindexJointOperatorToCanonicalCore, Matrix.reindex_apply]
      rw [VerifiedCircuitCore.embedSingleQubitOperator_apply]
      change (if VerifiedCircuitCore.agreesExcept (wireToCanonicalFin target)
          output input then
            VerifiedCircuitCore.localH (output (wireToCanonicalFin target))
              (input (wireToCanonicalFin target))
          else 0) =
        onWire target hMatrix (coreBasisToJoint output) (coreBasisToJoint input)
      rw [onWire_apply]
      by_cases agrees : VerifiedCircuitCore.agreesExcept
          (wireToCanonicalFin target) output input
      · have qAgrees := (agreesExcept_coreBasisToJoint_iff target output input).mp
          agrees
        rw [if_pos agrees, if_pos qAgrees]
        exact (congrFun (congrFun hMatrix_eq_coreLocalH
          (output (wireToCanonicalFin target)))
          (input (wireToCanonicalFin target))).symm
      · have qDiffers :
            ¬ SameOutside target (coreBasisToJoint output) (coreBasisToJoint input) :=
          fun qAgrees => agrees
            ((agreesExcept_coreBasisToJoint_iff target output input).mpr qAgrees)
        rw [if_neg agrees, if_neg qDiffers]
  | ry target angle =>
      simp only [PrimitiveGate.toCanonicalCore,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols,
        ProbabilityGeneratorQProof.primitiveGateOperator,
        reindexJointOperatorToCanonicalCore, Matrix.reindex_apply,
        AngleExpr.toCore_eval]
      rw [VerifiedCircuitCore.embedSingleQubitOperator_apply]
      change (if VerifiedCircuitCore.agreesExcept (wireToCanonicalFin target)
          output input then
            VerifiedCircuitCore.localRy angle.toReal
              (output (wireToCanonicalFin target))
              (input (wireToCanonicalFin target))
          else 0) =
        onWire target (ryMatrix angle.toReal)
          (coreBasisToJoint output) (coreBasisToJoint input)
      rw [onWire_apply]
      by_cases agrees : VerifiedCircuitCore.agreesExcept
          (wireToCanonicalFin target) output input
      · have qAgrees := (agreesExcept_coreBasisToJoint_iff target output input).mp
          agrees
        rw [if_pos agrees, if_pos qAgrees]
        exact (congrFun (congrFun (ryMatrix_eq_coreLocalRy angle.toReal)
          (output (wireToCanonicalFin target)))
          (input (wireToCanonicalFin target))).symm
      · have qDiffers :
            ¬ SameOutside target (coreBasisToJoint output) (coreBasisToJoint input) :=
          fun qAgrees => agrees
            ((agreesExcept_coreBasisToJoint_iff target output input).mpr qAgrees)
        rw [if_neg agrees, if_neg qDiffers]
  | cnot control target different =>
      simp only [PrimitiveGate.toCanonicalCore,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols,
        ProbabilityGeneratorQProof.primitiveGateOperator,
        reindexJointOperatorToCanonicalCore, Matrix.reindex_apply]
      rw [VerifiedCircuitCore.deterministicOperator_apply]
      change (if output = VerifiedCircuitCore.cnotBasisAction
          (wireToCanonicalFin control) (wireToCanonicalFin target) input
        then 1 else 0) =
        cnotMatrix control target different
          (coreBasisToJoint output) (coreBasisToJoint input)
      rw [cnotMatrix_apply_sparse]
      rw [← coreBasisToJoint_cnotBasisAction]
      by_cases equal : output = VerifiedCircuitCore.cnotBasisAction
          (wireToCanonicalFin control) (wireToCanonicalFin target) input
      · simp [equal]
      · have mappedDifferent :
            coreBasisToJoint output ≠ coreBasisToJoint
              (VerifiedCircuitCore.cnotBasisAction
                (wireToCanonicalFin control) (wireToCanonicalFin target) input) :=
          fun mappedEqual => equal
            ((jointBasisCoreEquiv ancillaQubits systemQubits).symm.injective
              mappedEqual)
        simp [equal, mappedDifferent]
  | toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      simp only [PrimitiveGate.toCanonicalCore,
        VerifiedCircuitCore.primitiveGateOperatorWithSymbols,
        ProbabilityGeneratorQProof.primitiveGateOperator,
        reindexJointOperatorToCanonicalCore, Matrix.reindex_apply]
      rw [VerifiedCircuitCore.deterministicOperator_apply]
      change (if output = VerifiedCircuitCore.toffoliBasisAction
          (wireToCanonicalFin control₁) (wireToCanonicalFin control₂)
          (wireToCanonicalFin target) input then 1 else 0) =
        toffoliMatrix control₁ control₂ target controlsDifferent firstDifferent
          secondDifferent (coreBasisToJoint output) (coreBasisToJoint input)
      rw [toffoliMatrix_apply_coreAdapter]
      rw [← coreBasisToJoint_toffoliBasisAction]
      by_cases equal : output = VerifiedCircuitCore.toffoliBasisAction
          (wireToCanonicalFin control₁) (wireToCanonicalFin control₂)
          (wireToCanonicalFin target) input
      · simp [equal]
      · have mappedDifferent :
            coreBasisToJoint output ≠ coreBasisToJoint
              (VerifiedCircuitCore.toffoliBasisAction
                (wireToCanonicalFin control₁) (wireToCanonicalFin control₂)
                (wireToCanonicalFin target) input) :=
          fun mappedEqual => equal
            ((jointBasisCoreEquiv ancillaQubits systemQubits).symm.injective
              mappedEqual)
        simp [equal, mappedDifferent]

/-- 任意Q回路の標準core compileは、Q全作用素の基底付け替えに一致する。 -/
theorem compileCircuitToCanonicalCore_denote
    {ancillaQubits systemQubits : Nat} :
    ∀ circuit : Circuit (PrimitiveGate ancillaQubits systemQubits),
      VerifiedCircuitCore.Circuit.denote
          (VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
          (circuit.mapGates PrimitiveGate.toCanonicalCore) =
        reindexJointOperatorToCanonicalCore
          (circuit.denote primitiveGateOperator) := by
  intro circuit
  exact VerifiedCircuitCore.Circuit.denote_mapGates_monoidHom
    primitiveGateOperator
    (VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
    PrimitiveGate.toCanonicalCore
    (Matrix.reindexRingEquiv ℂ
      (jointBasisCoreEquiv ancillaQubits systemQubits)).toMonoidHom
    primitiveGate_toCanonicalCore_operator
    circuit

/--
Transport a Q `JointBasis` exact component to the canonical shared-core basis.
The proof uses the child's `correct` field and the primitive compiler bridge.
-/
def reindexJointExactOperatorComponentToCanonicalCore
    {ancillaQubits systemQubits : Nat}
    (component : VerifiedCircuitCore.ExactOperatorComponent
      (primitiveGateOperator : PrimitiveGate ancillaQubits systemQubits →
        Operator (JointBasis ancillaQubits systemQubits))) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := ancillaQubits + systemQubits) internalZeroSymbolEnvironment) where
  circuit := component.circuit.mapGates PrimitiveGate.toCanonicalCore
  target := reindexJointOperatorToCanonicalCore component.target
  correct := calc
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
        (component.circuit.mapGates PrimitiveGate.toCanonicalCore) =
      reindexJointOperatorToCanonicalCore
        (component.circuit.denote primitiveGateOperator) :=
      compileCircuitToCanonicalCore_denote component.circuit
    _ = reindexJointOperatorToCanonicalCore component.target :=
      congrArg reindexJointOperatorToCanonicalCore component.correct

/-- 二段のgate mapは関数合成による一段のmapと同じASTになる。 -/
theorem circuit_mapGates_mapGates
    {Gate MiddleGate FinalGate : Type*}
    (second : MiddleGate → FinalGate) (first : Gate → MiddleGate) :
    ∀ circuit : VerifiedCircuitCore.Circuit Gate,
      (circuit.mapGates first).mapGates second =
        circuit.mapGates (second ∘ first) :=
  VerifiedCircuitCore.Circuit.mapGates_mapGates first second

end

end ProbabilityGeneratorQProof
