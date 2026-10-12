import Mathlib
import VerifiedMath.Basis

/-!
# 検証済み回路の最小線形代数基盤

有限基底上の状態、作用素、型安全な量子registerだけを定義する。
特定アルゴリズムや特定回路の名前は、このmoduleへ入れない。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 有限基底上の複素状態ベクトル。 -/
abbrev State (basis : Type*) := basis → ℂ

/-- 有限基底上の複素線形作用素を表す正方行列。 -/
abbrev Operator (basis : Type*) := Matrix basis basis ℂ

/-- 二つの作用素が一個の物理的に観測不能なglobal phaseを除いて一致する。 -/
def OperatorsEqualUpToGlobalPhase {basis : Type*}
    (actual target : Operator basis) : Prop :=
  ∃ angle : ℝ, actual = (Complex.exp (Complex.I * angle)) • target

/-- 二状態が一個の入力非依存global phaseを除いて一致する。 -/
def StatesEqualUpToGlobalPhase {basis : Type*}
    (actual target : State basis) : Prop :=
  ∃ angle : ℝ, actual = (Complex.exp (Complex.I * angle)) • target

/-- 作用素を状態ベクトルへ左から作用させる。 -/
def applyOperator {basis : Type*} [Fintype basis]
    (operator : Operator basis) (state : State basis) : State basis :=
  Matrix.mulVec operator state

/-- 一個の計算基底だけに振幅`1`を持つket。 -/
def basisKet {basis : Type*} [DecidableEq basis] (input : basis) : State basis :=
  VerifiedMath.Basis.vector input

/-- Compatibility boundary to the reusable mathematical basis vector. -/
theorem basisKet_eq_common {basis : Type*} [DecidableEq basis]
    (input : basis) :
    basisKet input = (VerifiedMath.Basis.vector input : basis → ℂ) := rfl

/-- Pointwise computation rule for the common computational-basis vector. -/
@[simp] theorem basisKet_apply {basis : Type*} [DecidableEq basis]
    (input candidate : basis) :
    basisKet input candidate = if candidate = input then 1 else 0 := rfl

/-- 行列積の状態作用は、二つの状態作用の逐次合成に等しい。 -/
theorem applyOperator_mul
    {basis : Type*} [Fintype basis]
    (second first : Operator basis) (state : State basis) :
    applyOperator (second * first) state =
      applyOperator second (applyOperator first state) := by
  exact (Matrix.mulVec_mulVec state second first).symm

/-- 作用素は零状態を零状態へ写す。 -/
@[simp] theorem applyOperator_zero
    {basis : Type*} [Fintype basis]
    (operator : Operator basis) :
    applyOperator operator (0 : State basis) = 0 := by
  funext output
  simp [applyOperator, Matrix.mulVec, dotProduct]

/-- 作用素の状態への作用は加法を保存する。 -/
theorem applyOperator_add
    {basis : Type*} [Fintype basis]
    (operator : Operator basis) (left right : State basis) :
    applyOperator operator (left + right) =
      applyOperator operator left + applyOperator operator right := by
  funext output
  simp [applyOperator, Matrix.mulVec, dotProduct, mul_add,
    Finset.sum_add_distrib]

/-- 作用素の状態への作用は複素数スカラー倍を保存する。 -/
theorem applyOperator_smul
    {basis : Type*} [Fintype basis]
    (operator : Operator basis) (scalar : ℂ) (state : State basis) :
    applyOperator operator (scalar • state) =
      scalar • applyOperator operator state := by
  funext output
  change (∑ input, operator output input * (scalar * state input)) =
    scalar * ∑ input, operator output input * state input
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  ring

/-- 基底ketへ作用させた振幅は、作用素の対応する行列要素である。 -/
@[simp] theorem applyOperator_basisKet
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) (input output : basis) :
    applyOperator operator (basisKet input) output = operator output input := by
  simp [applyOperator, basisKet, Matrix.mulVec, dotProduct]

/-- 置換行列の状態作用は状態関数への置換の前合成である。 -/
theorem applyOperator_permMatrix
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis) (state : State basis) :
    applyOperator (permutation.permMatrix ℂ) state =
      state ∘ permutation := by
  exact Matrix.permMatrix_mulVec permutation

/-- `qubits`量子ビットの計算基底。 -/
abbrev QubitBasis (qubits : Nat) := Fin qubits → Bool

/-- 全体wire集合の中から相異なる`width`本を選ぶ型安全なregister。 -/
structure Register (qubits width : Nat) where
  /-- register内添字から物理wireへの写像。 -/
  wire : Fin width → Fin qubits
  /-- register内の異なる添字は異なる物理wireを指す。 -/
  injective : Function.Injective wire

/-- A duplicate-free physical-wire list of a specified length, viewed as an
injective typed wire placement. -/
def wireEmbeddingOfNodupList {total sourceWidth : Nat}
    (wires : List (Fin total)) (length_eq : wires.length = sourceWidth)
    (nodup : wires.Nodup) : Fin sourceWidth ↪ Fin total :=
  length_eq ▸
    { toFun := wires.get
      inj' := fun _ _ equal => nodup.get_inj_iff.mp equal }

/-- Enumerating the typed placement constructed from a duplicate-free list
recovers the original source-order wire list. -/
@[simp] theorem wireEmbeddingOfNodupList_ofFn {total sourceWidth : Nat}
    (wires : List (Fin total)) (length_eq : wires.length = sourceWidth)
    (nodup : wires.Nodup) :
    List.ofFn (wireEmbeddingOfNodupList wires length_eq nodup) = wires := by
  cases length_eq
  simp [wireEmbeddingOfNodupList]

/-- 計算基底からregisterに属するbit列だけを読む。 -/
def Register.read {qubits width : Nat}
    (register : Register qubits width) (basis : QubitBasis qubits) :
    QubitBasis width :=
  fun index => basis (register.wire index)

/-- success基底の埋込みから作用素のsuccess blockを切り出す。 -/
def successBlock {fullBasis systemBasis : Type*}
    (embed : systemBasis → fullBasis) (operator : Operator fullBasis) :
    Operator systemBasis :=
  fun output input => operator (embed output) (embed input)

/-- 実行順の作用素列を、先頭作用素が最初に作用する積として合成する。 -/
def operatorSequence {M : Type*} [Monoid M] : List M → M
  | [] => 1
  | first :: rest => operatorSequence rest * first

/-- An execution-order product of unitary operators is unitary. -/
theorem operatorSequence_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operators : List (Operator basis))
    (each : ∀ operator ∈ operators,
      operator ∈ Matrix.unitaryGroup basis ℂ) :
    operatorSequence operators ∈ Matrix.unitaryGroup basis ℂ := by
  induction operators with
  | nil =>
      simp [operatorSequence]
  | cons first rest inductionHypothesis =>
      simp only [operatorSequence]
      exact Submonoid.mul_mem _
        (inductionHypothesis fun operator member =>
          each operator (by simp [member]))
        (each first (by simp))

/-- A multiplicative homomorphism preserves execution-order products. -/
theorem MonoidHom.map_operatorSequence
    {M N : Type*} [Monoid M] [Monoid N]
    (hom : M →* N) (values : List M) :
    hom (operatorSequence values) =
      operatorSequence (values.map hom) := by
  induction values with
  | nil => simp [operatorSequence]
  | cons first rest inductionHypothesis =>
      simp [operatorSequence, inductionHypothesis]

/-- 実行順作用素列の append は、後半積を左から掛ける積へ分解できる。 -/
theorem operatorSequence_append
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (left right : List (Operator basis)) :
    operatorSequence (left ++ right) =
      operatorSequence right * operatorSequence left := by
  induction left with
  | nil => simp [operatorSequence]
  | cons first rest inductionHypothesis =>
      simp only [List.cons_append, operatorSequence]
      rw [inductionHypothesis]
      simp only [mul_assoc]

end

end VerifiedCircuitCore
