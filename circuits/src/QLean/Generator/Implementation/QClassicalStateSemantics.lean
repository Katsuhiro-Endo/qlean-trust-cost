import QLean.Generator.Implementation.AlignCircuitCorrectness
import QLean.Generator.Implementation.QTopLevelCorrectness
import QLean.Generator.Implementation.UQCircuit

/-!
# Q回路の可逆部分に対する状態意味論

COPY、column/row oracle、整列、終端Xを密行列として展開せず、計算基底置換による
状態関数の合成へ一度に書き換える補題をまとめる。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- COPYを任意状態へ作用させると、状態関数へCOPYの逆置換を合成したものになる。 -/
theorem xorSystemIntoColumnKeyPrimitiveCircuit_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        ((xorSystemIntoColumnKeyPrimitiveCircuit p).toIdealOperator primitiveGateOperator)
        state =
      state ∘ (xorSystemIntoColumnKeyReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation := by
  rw [xorSystemIntoColumnKeyPrimitiveCircuit_eq_reversible]
  exact reversibleCircuit_applyOperator _ _

/-- column oracleを任意状態へ作用させると、状態関数へoracleの逆置換を合成したものになる。 -/
theorem applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        ((applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).toIdealOperator primitiveGateOperator) state =
      state ∘ (applyColumnOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation
        reversibleGatePermutation := by
  exact reversibleCircuit_applyOperator _ _

/-- row oracleを任意状態へ作用させると、状態関数へoracleの逆置換を合成したものになる。 -/
theorem applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        ((applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p).toIdealOperator primitiveGateOperator) state =
      state ∘ (applyRowOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation
        reversibleGatePermutation := by
  exact reversibleCircuit_applyOperator _ _

/-- column oracle逆回路の状態作用は、正方向の実行置換を状態関数へ合成する。 -/
theorem columnOracleReverse_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        (((applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).reverse PrimitiveGate.inverse).toIdealOperator
          primitiveGateOperator) state =
      state ∘ (applyColumnOracleReferenceAndRestoreWorkCircuit p).toExecutionPermutation
        reversibleGatePermutation := by
  rw [reverseColumnOracleIdealOperator_eq_adjoint]
  rw [show (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).toIdealOperator primitiveGateOperator =
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation
        reversibleGatePermutation).permMatrix ℂ by
        exact ReversibleCircuit.toPrimitive_operator_eq_permMatrix _]
  rw [Matrix.conjTranspose_permMatrix]
  rw [applyOperator_permMatrix]
  rw [Circuit.toBasisPermutation_eq_execution_inverse
    reversibleGatePermutation (by intro gate; cases gate <;> rfl)]
  simp

/-- 整列回路の状態作用は、その可逆基底逆置換との関数合成である。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator ((controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p).toIdealOperator primitiveGateOperator) state =
      state ∘ (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation := by
  rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_eq_reversible]
  exact reversibleCircuit_applyOperator _ _

/-- 終端Xの状態作用は、その基底反転との関数合成である。 -/
theorem flipAmplitudeSignalPrimitiveCircuit_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        ((flipAmplitudeSignalPrimitiveCircuit p).toIdealOperator primitiveGateOperator) state =
      state ∘ (flipAmplitudeSignalReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation := by
  rw [flipAmplitudeSignalPrimitiveCircuit_eq_reversible]
  exact reversibleCircuit_applyOperator _ _

end

end ProbabilityGeneratorQProof
