import QLean.Generator.Implementation.QOracleCorrectness

/-!
# 一量子ビット作用の疎な振幅意味論

任意幅の全体行列作用を、対象wireの0・1に対応する二項だけへ縮約する。
量子ビット数に依存する基底列挙は行わず、`splitWireEquiv`による有限和の付替えを使う。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 基底状態の指定wireだけを与えたBool値へ置き換える。 -/
def replaceWire
    {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits)
    (target : Wire ancillaQubits systemQubits) (value : Bool) :
    JointBasis ancillaQubits systemQubits :=
  fun wire => if wire = target then value else basis wire

/-- 置換した基底を対象wireで読むと指定値になる。 -/
@[simp] theorem replaceWire_target
    {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits)
    (target : Wire ancillaQubits systemQubits) (value : Bool) :
    replaceWire basis target value target = value := by
  simp [replaceWire]

/-- 置換対象以外のwire値は変化しない。 -/
@[simp] theorem replaceWire_other
    {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits)
    (target wire : Wire ancillaQubits systemQubits) (value : Bool)
    (different : wire ≠ target) :
    replaceWire basis target value wire = basis wire := by
  simp [replaceWire, different]

/-- `replaceWire`は`splitWireEquiv`の逆写像を同じ外側基底へ適用したものに等しい。 -/
theorem replaceWire_eq_splitWireEquiv_symm
    {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits)
    (target : Wire ancillaQubits systemQubits) (value : Bool) :
    replaceWire basis target value =
      (splitWireEquiv target).symm
        (value, (splitWireEquiv target basis).2) := by
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [replaceWire, splitWireEquiv]
  · change (if _ : wire = target then value else basis wire) =
      (if equal' : wire = target then value else
        (splitWireEquiv target basis).2 ⟨wire, equal'⟩)
    simp [equal, splitWireEquiv]

/-- wire分解を戻した基底の対象wireは、分解対の第一成分である。 -/
@[simp] theorem splitWireEquiv_symm_target
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (bit : Bool)
    (outside : {wire : Wire ancillaQubits systemQubits // wire ≠ target} → Bool) :
    (splitWireEquiv target).symm (bit, outside) target = bit := by
  have inverse := congrArg Prod.fst
    ((splitWireEquiv target).apply_symm_apply (bit, outside))
  exact inverse

/-- wire分解を戻した基底が外側で一致することは、第二成分の一致と同値である。 -/
theorem sameOutside_splitWireEquiv_symm
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (output : JointBasis ancillaQubits systemQubits)
    (bit : Bool)
    (outside : {wire : Wire ancillaQubits systemQubits // wire ≠ target} → Bool) :
    SameOutside target output ((splitWireEquiv target).symm (bit, outside)) ↔
      outside = (splitWireEquiv target output).2 := by
  rw [← restrictedBasis_eq_iff_sameOutside]
  change (splitWireEquiv target output).2 =
      (splitWireEquiv target ((splitWireEquiv target).symm (bit, outside))).2 ↔ _
  rw [(splitWireEquiv target).apply_symm_apply]
  exact eq_comm

/--
任意幅で一量子ビット作用素を状態へ適用した振幅は、対象入力bitの二値だけの和になる。
-/
theorem applyOperator_onWire
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (operator : Operator Bool)
    (state : JointBasis ancillaQubits systemQubits → ℂ)
    (output : JointBasis ancillaQubits systemQubits) :
    applyOperator (onWire target operator) state output =
      ∑ inputBit : Bool,
        operator (output target) inputBit *
          state (replaceWire output target inputBit) := by
  unfold applyOperator VerifiedCircuitCore.applyOperator Matrix.mulVec dotProduct
  rw [show (∑ input,
      onWire target operator output input * state input) =
        ∑ pair : Bool ×
            ({wire : Wire ancillaQubits systemQubits // wire ≠ target} → Bool),
          onWire target operator output ((splitWireEquiv target).symm pair) *
            state ((splitWireEquiv target).symm pair) by
    exact ((splitWireEquiv target).symm.sum_comp fun input =>
      onWire target operator output input * state input).symm]
  simp_rw [Fintype.sum_prod_type]
  simp [onWire_apply, sameOutside_splitWireEquiv_symm,
    replaceWire_eq_splitWireEquiv_symm]

/-- 置換行列を一般作用素の左から掛けると出力添字だけが置換される。 -/
theorem permMatrix_mul_operator_apply
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis) (operator : Operator basis)
    (output input : basis) :
    (permutation.permMatrix ℂ * operator) output input =
      operator (permutation output) input := by
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix]

/-- 一般作用素の右から置換行列を掛けると入力添字だけが逆置換される。 -/
theorem operator_mul_permMatrix_apply
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) (permutation : Equiv.Perm basis)
    (output input : basis) :
    (operator * permutation.permMatrix ℂ) output input =
      operator output (permutation.symm input) := by
  change
    Matrix.vecMul (fun middle => operator output middle)
        (permutation.permMatrix ℂ) input = _
  rw [Matrix.vecMul_permMatrix]
  rfl

/-- 自己逆置換で作用素を挟むと、入出力添字の両方へ同じ置換が作用する。 -/
theorem permMatrix_conjugate_operator_apply
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis)
    (involutive : permutation.symm = permutation)
    (operator : Operator basis) (output input : basis) :
    (permutation.permMatrix ℂ * operator * permutation.permMatrix ℂ)
        output input =
      operator (permutation output) (permutation input) := by
  rw [operator_mul_permMatrix_apply, permMatrix_mul_operator_apply]
  rw [involutive]

/-- 逐次回路の状態作用は、第一回路の作用後に第二回路を作用させる。 -/
theorem applyOperator_toIdealOperator_seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (first second : Circuit Gate) (state : basis → ℂ) :
    applyOperator ((Circuit.seq first second).toIdealOperator gateOperator) state =
      applyOperator (second.toIdealOperator gateOperator)
        (applyOperator (first.toIdealOperator gateOperator) state) := by
  unfold applyOperator VerifiedCircuitCore.applyOperator
  change
    (second.toIdealOperator gateOperator * first.toIdealOperator gateOperator) *ᵥ state =
      second.toIdealOperator gateOperator *ᵥ
        (first.toIdealOperator gateOperator *ᵥ state)
  exact (Matrix.mulVec_mulVec state
    (second.toIdealOperator gateOperator)
    (first.toIdealOperator gateOperator)).symm

/-- 回路リストの連結作用は、状態作用を実行順に左畳み込みしたものに等しい。 -/
theorem applyOperator_toIdealOperator_sequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (circuits : List (Circuit Gate)) (state : basis → ℂ) :
    applyOperator ((Circuit.sequence circuits).toIdealOperator gateOperator) state =
      circuits.foldl
        (fun current circuit =>
          applyOperator (circuit.toIdealOperator gateOperator) current)
        state := by
  induction circuits generalizing state with
  | nil =>
      rw [Circuit.sequence_nil]
      change Matrix.mulVec (1 : Operator basis) state = state
      simp
  | cons circuit circuits inductionHypothesis =>
      rw [Circuit.sequence_cons]
      rw [applyOperator_toIdealOperator_seq]
      exact inductionHypothesis _

end

end ProbabilityGeneratorQProof
