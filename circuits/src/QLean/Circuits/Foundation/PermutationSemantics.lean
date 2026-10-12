import QLean.Circuits.Foundation.Circuit

/-!
# 計算基底置換意味論

可逆gate回路を計算基底上の置換として評価し、置換行列意味論と接続する。
-/

namespace VerifiedCircuitCore

noncomputable section

namespace Circuit

/-- 回路を実行順に合成した計算基底置換へ解釈する。 -/
def toExecutionPermutation {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) :
    Circuit Gate → Equiv.Perm basis
  | .identity => 1
  | .gate value => gatePermutation value
  | .seq first second =>
      toExecutionPermutation gatePermutation second *
        toExecutionPermutation gatePermutation first
  | .repeat count body => (toExecutionPermutation gatePermutation body) ^ count

/-- Compose gate permutations in the order induced by permutation-matrix
multiplication.  This is the opposite product convention from direct basis
execution at a sequential node. -/
def toCompositionPermutation {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) :
    Circuit Gate → Equiv.Perm basis
  | .identity => 1
  | .gate value => gatePermutation value
  | .seq first second =>
      toCompositionPermutation gatePermutation first *
        toCompositionPermutation gatePermutation second
  | .repeat count body =>
      (toCompositionPermutation gatePermutation body) ^ count

/-- 可逆回路を計算基底一個へ実行する関数意味論。 -/
def runBasis {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (circuit : Circuit Gate) (input : basis) : basis :=
  circuit.toExecutionPermutation gatePermutation input

/-- gate列回路の基底作用は、gate置換を左から実行するfoldである。 -/
theorem runBasis_fromList
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (gates : List Gate) (input : basis) :
    (Circuit.fromList gates).runBasis gatePermutation input =
      gates.foldl (fun state gate => gatePermutation gate state) input := by
  induction gates generalizing input with
  | nil => simp [Circuit.fromList, runBasis, toExecutionPermutation]
  | cons gate rest inductionHypothesis =>
      change (Circuit.fromList rest).runBasis gatePermutation
          (gatePermutation gate input) = _
      exact inductionHypothesis _

/-- 回路列の基底作用は、子回路の基底作用を左から実行するfoldである。 -/
theorem runBasis_sequence
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (circuits : List (Circuit Gate)) (input : basis) :
    (Circuit.sequence circuits).runBasis gatePermutation input =
      circuits.foldl
        (fun state circuit => circuit.runBasis gatePermutation state) input := by
  induction circuits generalizing input with
  | nil => rfl
  | cons circuit rest inductionHypothesis =>
      change (Circuit.sequence rest).runBasis gatePermutation
          (circuit.runBasis gatePermutation input) = _
      exact inductionHypothesis _

/-- 各gateの逆が逆置換なら、逆回路は合成済み置換の逆である。 -/
theorem toExecutionPermutation_reverse
    {Gate basis : Type*}
    (inverseGate : Gate → Gate)
    (gatePermutation : Gate → Equiv.Perm basis)
    (inverseCorrect : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹) :
    ∀ circuit : Circuit Gate,
      (circuit.reverse inverseGate).toExecutionPermutation gatePermutation =
        (circuit.toExecutionPermutation gatePermutation)⁻¹
  | .identity => by simp [Circuit.reverse, toExecutionPermutation]
  | .gate value => inverseCorrect value
  | .seq first second => by
      simp [Circuit.reverse, toExecutionPermutation,
        toExecutionPermutation_reverse inverseGate gatePermutation inverseCorrect first,
        toExecutionPermutation_reverse inverseGate gatePermutation inverseCorrect second]
  | .repeat count body => by
      simp [Circuit.reverse, toExecutionPermutation,
        toExecutionPermutation_reverse inverseGate gatePermutation inverseCorrect body]

/-- C-U-U回路の基底作用をcompute逆・use・computeの合成として読む。 -/
theorem runBasis_computeUseUncompute
    {Gate basis : Type*}
    (inverseGate : Gate → Gate)
    (gatePermutation : Gate → Equiv.Perm basis)
    (inverseCorrect : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹)
    (compute use : Circuit Gate) (input : basis) :
    (computeUseUncompute inverseGate compute use).runBasis gatePermutation input =
      (compute.toExecutionPermutation gatePermutation)⁻¹
        (use.toExecutionPermutation gatePermutation
          (compute.toExecutionPermutation gatePermutation input)) := by
  simp [runBasis, computeUseUncompute, toExecutionPermutation,
    toExecutionPermutation_reverse inverseGate gatePermutation inverseCorrect]

/-- If the use stage maps a computed input to the computed image of another
input, the uncompute stage restores exactly that other input. -/
theorem computeUseUncompute_clean
    {Gate basis : Type*}
    (inverseGate : Gate → Gate)
    (gatePermutation : Gate → Equiv.Perm basis)
    (inverseCorrect : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹)
    (compute use : Circuit Gate) (input output : basis)
    (useResult :
      use.toExecutionPermutation gatePermutation
          (compute.toExecutionPermutation gatePermutation input) =
        compute.toExecutionPermutation gatePermutation output) :
    (computeUseUncompute inverseGate compute use).runBasis gatePermutation input =
      output := by
  rw [runBasis_computeUseUncompute inverseGate gatePermutation inverseCorrect,
    useResult]
  simp

/-- gate置換を置換行列へ持ち上げた回路意味論。 -/
def permutationGateOperator {Gate basis : Type*} [DecidableEq basis]
    (gatePermutation : Gate → Equiv.Perm basis) : Gate → Operator basis :=
  fun value => (gatePermutation value)⁻¹.permMatrix ℂ

/-- Evaluating permutation matrices follows the matrix-composition
permutation stored by `toCompositionPermutation`. -/
theorem denote_permMatrix_eq_toCompositionPermutation
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gatePermutation : Gate → Equiv.Perm basis) :
    ∀ circuit : Circuit Gate,
      circuit.denote (fun gate => (gatePermutation gate).permMatrix ℂ) =
        (circuit.toCompositionPermutation gatePermutation).permMatrix ℂ
  | .identity => by simp [denote, toCompositionPermutation]
  | .gate value => rfl
  | .seq first second => by
      simp only [denote_seq, toCompositionPermutation,
        denote_permMatrix_eq_toCompositionPermutation gatePermutation first,
        denote_permMatrix_eq_toCompositionPermutation gatePermutation second]
      rw [Matrix.permMatrix_mul]
  | .repeat count body => by
      simp only [denote_repeat, toCompositionPermutation,
        denote_permMatrix_eq_toCompositionPermutation gatePermutation body]
      induction count with
      | zero => simp
      | succ count inductionHypothesis =>
          rw [pow_succ, pow_succ', Matrix.permMatrix_mul, inductionHypothesis]

/-- When every gate permutation is self-inverse, matrix-composition order is
the inverse of direct execution order. -/
theorem toCompositionPermutation_eq_execution_inverse
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (gateInvolutive : ∀ gate,
      gatePermutation gate = (gatePermutation gate)⁻¹) :
    ∀ circuit : Circuit Gate,
      circuit.toCompositionPermutation gatePermutation =
        (circuit.toExecutionPermutation gatePermutation)⁻¹
  | .identity => by
      simp [toCompositionPermutation, toExecutionPermutation]
  | .gate value => gateInvolutive value
  | .seq first second => by
      simp [toCompositionPermutation, toExecutionPermutation,
        toCompositionPermutation_eq_execution_inverse
          gatePermutation gateInvolutive first,
        toCompositionPermutation_eq_execution_inverse
          gatePermutation gateInvolutive second]
  | .repeat count body => by
      simp [toCompositionPermutation, toExecutionPermutation,
        toCompositionPermutation_eq_execution_inverse
          gatePermutation gateInvolutive body]

/-- 置換行列による回路評価は、構文順に合成した置換行列に等しい。 -/
theorem denote_permutationGateOperator
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gatePermutation : Gate → Equiv.Perm basis) :
    ∀ circuit : Circuit Gate,
      circuit.denote (permutationGateOperator gatePermutation) =
        (circuit.toExecutionPermutation gatePermutation)⁻¹.permMatrix ℂ
  | .identity => by simp [denote, toExecutionPermutation]
  | .gate value => by simp [denote, toExecutionPermutation, permutationGateOperator]
  | .seq first second => by
      simp only [denote_seq, toExecutionPermutation,
        denote_permutationGateOperator gatePermutation first,
        denote_permutationGateOperator gatePermutation second]
      rw [mul_inv_rev, Matrix.permMatrix_mul]
  | .repeat count body => by
      simp only [denote_repeat, toExecutionPermutation,
        denote_permutationGateOperator gatePermutation body]
      induction count with
      | zero => simp
      | succ count inductionHypothesis =>
          rw [pow_succ, pow_succ, inductionHypothesis]
          rw [← Matrix.permMatrix_mul]
          simp only [mul_inv_rev]

end Circuit

end

end VerifiedCircuitCore
