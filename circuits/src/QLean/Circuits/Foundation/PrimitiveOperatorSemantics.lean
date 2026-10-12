import QLean.Circuits.Foundation.Foundations

/-!
# 基本ゲートの回路非依存な解析意味論

角度式、局所行列、wire 埋込み、および決定的基底作用を定義する。
この module は回路構文木や回路 denotation を参照しない。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 数値化前の角度を保持する実行可能な記号式。 -/
inductive AngleExpr where
  /-- Lean 内部で既に検証された実数定数。 -/
  | const (value : ℝ)
  /-- 分母の正値証明を伴う有理数。 -/
  | rational (numerator : Int) (denominator : Nat)
      (denominatorPositive : 0 < denominator)
  /-- 整数 mantissa を `10 ^ scale` で割る厳密な有限小数。 -/
  | decimal (mantissa : Int) (scale : Nat)
  /-- 外部の記号環境から値を受け取る変数。 -/
  | symbol (name : String)
  /-- 円周率。 -/
  | pi
  /-- 和。 -/
  | add (left right : AngleExpr)
  /-- 積。 -/
  | mul (left right : AngleExpr)
  /-- 商。 -/
  | div (left right : AngleExpr)
  /-- 符号反転。 -/
  | neg (value : AngleExpr)
  /-- 平方根。 -/
  | sqrt (value : AngleExpr)
  /-- 逆余弦。 -/
  | acos (value : AngleExpr)

/-- An angle expression is symbol-free when its value is fixed without an
external manifest environment. -/
def AngleExpr.IsSymbolFree : AngleExpr → Prop
  | .const _ | .rational _ _ _ | .decimal _ _ | .pi => True
  | .symbol _ => False
  | .add left right | .mul left right | .div left right =>
      left.IsSymbolFree ∧ right.IsSymbolFree
  | .neg value | .sqrt value | .acos value => value.IsSymbolFree

/-- 記号環境を受け取り角度式を厳密な実数へ解釈する。 -/
def AngleExpr.eval (symbolValue : String → ℝ) : AngleExpr → ℝ
  | .const value => value
  | .rational numerator denominator _ => (numerator : ℝ) / (denominator : ℝ)
  | .decimal mantissa scale => (mantissa : ℝ) / (10 : ℝ) ^ scale
  | .symbol name => symbolValue name
  | .pi => Real.pi
  | .add left right => left.eval symbolValue + right.eval symbolValue
  | .mul left right => left.eval symbolValue * right.eval symbolValue
  | .div left right => left.eval symbolValue / right.eval symbolValue
  | .neg value => -value.eval symbolValue
  | .sqrt value => Real.sqrt (value.eval symbolValue)
  | .acos value => Real.arccos (value.eval symbolValue)

/-- A symbol-free angle evaluates identically in every symbol environment. -/
theorem AngleExpr.eval_eq_of_isSymbolFree
    (expression : AngleExpr) (symbolFree : expression.IsSymbolFree)
    (first second : String → ℝ) :
    expression.eval first = expression.eval second := by
  induction expression with
  | const | rational | decimal | pi => rfl
  | symbol name => simp [AngleExpr.IsSymbolFree] at symbolFree
  | add left right leftInduction rightInduction =>
      exact congrArg₂ (· + ·)
        (leftInduction symbolFree.1) (rightInduction symbolFree.2)
  | mul left right leftInduction rightInduction =>
      exact congrArg₂ (· * ·)
        (leftInduction symbolFree.1) (rightInduction symbolFree.2)
  | div left right leftInduction rightInduction =>
      exact congrArg₂ (· / ·)
        (leftInduction symbolFree.1) (rightInduction symbolFree.2)
  | neg value inductionHypothesis =>
      exact congrArg Neg.neg (inductionHypothesis symbolFree)
  | sqrt value inductionHypothesis =>
      exact congrArg Real.sqrt (inductionHypothesis symbolFree)
  | acos value inductionHypothesis =>
      exact congrArg Real.arccos (inductionHypothesis symbolFree)

/-- 実数定数の評価は格納値に等しい。 -/
@[simp] theorem AngleExpr.eval_const (symbolValue : String → ℝ) (value : ℝ) :
    (AngleExpr.const value).eval symbolValue = value := rfl

/-- 有限小数の評価は整数と十進 scale から一意に決まる。 -/
@[simp] theorem AngleExpr.eval_decimal (symbolValue : String → ℝ)
    (mantissa : Int) (scale : Nat) :
    (AngleExpr.decimal mantissa scale).eval symbolValue =
      (mantissa : ℝ) / (10 : ℝ) ^ scale := rfl

/-- 符号反転した角度式は評価値も符号反転する。 -/
@[simp] theorem AngleExpr.eval_neg (symbolValue : String → ℝ) (value : AngleExpr) :
    (AngleExpr.neg value).eval symbolValue = -value.eval symbolValue := rfl

/-- 指定 wire 以外の全 bit が二つの基底で一致することを表す。 -/
def agreesExcept {qubits : Nat} (target : Fin qubits)
    (output input : QubitBasis qubits) : Prop :=
  ∀ wire, wire ≠ target → output wire = input wire

/-- 指定した二 wire 以外の全 bit が二つの基底で一致することを表す。 -/
def agreesExceptTwo {qubits : Nat} (first second : Fin qubits)
    (output input : QubitBasis qubits) : Prop :=
  ∀ wire, wire ≠ first → wire ≠ second → output wire = input wire

/-- 一つの wire と残りの wire を分離する基底同値。 -/
def splitWireEquiv {qubits : Nat} (target : Fin qubits) :
    QubitBasis qubits ≃ Bool × ({wire : Fin qubits // wire ≠ target} → Bool) where
  toFun basis := (basis target, fun wire => basis wire.1)
  invFun pair := fun wire =>
    if equal : wire = target then pair.1 else pair.2 ⟨wire, equal⟩
  left_inv basis := by
    funext wire
    by_cases equal : wire = target
    · subst wire
      simp
    · simp [equal]
  right_inv pair := by
    apply Prod.ext
    · simp
    · funext wire
      simp [wire.2]

/-- 二つの相異なる wire と残りの wire を分離する基底同値。 -/
def splitTwoWiresEquiv {qubits : Nat} (first second : Fin qubits)
    (different : first ≠ second) :
    QubitBasis qubits ≃
      (Bool × Bool) ×
        ({wire : Fin qubits // wire ≠ first ∧ wire ≠ second} → Bool) where
  toFun basis := ((basis first, basis second), fun wire => basis wire.1)
  invFun pair := fun wire =>
    if firstEqual : wire = first then pair.1.1
    else if secondEqual : wire = second then pair.1.2
    else pair.2 ⟨wire, firstEqual, secondEqual⟩
  left_inv basis := by
    funext wire
    by_cases firstEqual : wire = first
    · subst wire
      simp
    · by_cases secondEqual : wire = second
      · subst wire
        simp [firstEqual]
      · simp [firstEqual, secondEqual]
  right_inv pair := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [Ne.symm different]
    · funext wire
      simp [wire.2.1, wire.2.2]

/-- 一量子ビット局所行列を指定 wire へ埋め込む。 -/
def embedSingleQubitOperator {qubits : Nat} (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  Matrix.reindex (splitWireEquiv target).symm (splitWireEquiv target).symm
    (Matrix.kronecker localOperator
      (1 : Operator ({wire : Fin qubits // wire ≠ target} → Bool)))

/-- 二量子ビット局所行列を指定した相異なる二 wire へ埋め込む。 -/
def embedTwoQubitOperator {qubits : Nat} (first second : Fin qubits)
    (different : first ≠ second)
    (localOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Operator (QubitBasis qubits) :=
  Matrix.reindex (splitTwoWiresEquiv first second different).symm
    (splitTwoWiresEquiv first second different).symm
    (Matrix.kronecker localOperator
      (1 : Operator
        ({wire : Fin qubits // wire ≠ first ∧ wire ≠ second} → Bool)))

/-- control が一のときだけ target 側の局所行列を適用する二量子ビット行列。 -/
def localControlledOperator (localOperator : Matrix Bool Bool ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun output input =>
    if output.1 ≠ input.1 then 0
    else if input.1 then localOperator output.2 input.2
    else if output.2 = input.2 then 1 else 0

/-- 制御付き一量子ビット局所行列を相異なる control/target wire へ埋め込む。 -/
def embedControlledSingleQubitOperator {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  embedTwoQubitOperator control target different
    (localControlledOperator localOperator)

/-- The extensional outside-wire relation is propositionally decidable.  We
keep this instance local to the pure specification module rather than exposing
classical decidability as an additional public premise. -/
local instance predicateControlledAgreesExceptDecidable {qubits : Nat}
    (target : Fin qubits) (output input : QubitBasis qubits) :
    Decidable (agreesExcept target output input) :=
  Classical.propDecidable _

/--
Apply a one-qubit local operator at `target` exactly when an independently
stated Boolean predicate on the input basis is true.  This is a mathematical
specification operator: it does not introduce a predicate-computation circuit
or any work wire.  For a unitary interpretation the caller additionally proves
that the predicate is independent of `target`.
-/
def predicateControlledSingleQubitOperator {qubits : Nat}
    (predicate : QubitBasis qubits → Bool) (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  fun output input =>
    if agreesExcept target output input then
      if predicate input then localOperator (output target) (input target)
      else if output target = input target then 1 else 0
    else 0

/-- A predicate is independent of the target wire when changing only that
wire cannot change the predicate value. -/
def PredicateIndependentOfWire {qubits : Nat}
    (predicate : QubitBasis qubits → Bool) (target : Fin qubits) : Prop :=
  ∀ first second, agreesExcept target first second →
    predicate first = predicate second

@[simp] theorem predicateControlledSingleQubitOperator_apply
    {qubits : Nat} (predicate : QubitBasis qubits → Bool)
    (target : Fin qubits) (localOperator : Matrix Bool Bool ℂ)
    (output input : QubitBasis qubits) :
    predicateControlledSingleQubitOperator predicate target localOperator
        output input =
      if agreesExcept target output input then
        if predicate input then localOperator (output target) (input target)
        else if output target = input target then 1 else 0
      else 0 := rfl

/-- The false predicate gives the identity action extensionally. -/
theorem predicateControlledSingleQubitOperator_false
    {qubits : Nat} (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ) :
    predicateControlledSingleQubitOperator (fun _ => false) target
        localOperator = 1 := by
  classical
  funext output input
  by_cases outside : agreesExcept target output input
  · by_cases targetEqual : output target = input target
    · have basisEqual : output = input := by
        funext wire
        by_cases equal : wire = target
        · subst wire
          exact targetEqual
        · exact outside wire equal
      subst output
      rw [predicateControlledSingleQubitOperator_apply]
      simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
      have selfOutside : agreesExcept target input input := fun _ _ => rfl
      exact if_pos selfOutside
    · have basisDifferent : output ≠ input := by
        intro equal
        exact targetEqual (congrFun equal target)
      simp [predicateControlledSingleQubitOperator, outside, targetEqual,
        basisDifferent]
  · have basisDifferent : output ≠ input := by
      intro equal
      subst output
      exact outside (fun _ _ => rfl)
    simp [predicateControlledSingleQubitOperator, outside, basisDifferent]

/-- 基底関数を 0-1 の置換型行列へ持ち上げる。 -/
def deterministicOperator {basis : Type*} [DecidableEq basis]
    (action : basis → basis) : Operator basis :=
  fun output input => if output = action input then 1 else 0

/-- `deterministicOperator`の行列要素は定義した基底作用そのものである。 -/
@[simp] theorem deterministicOperator_apply
    {basis : Type*} [DecidableEq basis]
    (action : basis → basis) (output input : basis) :
    deterministicOperator action output input =
      if output = action input then 1 else 0 := rfl

/-- 決定的0-1作用素は基底ketを基底関数の像へ移す。 -/
theorem applyOperator_deterministicOperator_basisKet
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (action : basis → basis) (input : basis) :
    applyOperator (deterministicOperator action) (basisKet input) =
      basisKet (action input) := by
  funext output
  rw [applyOperator_basisKet]
  rfl

/-- 指定 wire を Bool 値だけ XOR 更新する。 -/
def xorWire {qubits : Nat} (target : Fin qubits) (value : Bool)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  Function.update input target (input target != value)

/-- `xorWire` applies the requested XOR at its target. -/
@[simp] theorem xorWire_apply_same {qubits : Nat} (target : Fin qubits)
    (value : Bool) (input : QubitBasis qubits) :
    xorWire target value input target = (input target != value) := by
  simp [xorWire]

/-- `xorWire` preserves every other wire. -/
@[simp] theorem xorWire_apply_other {qubits : Nat} (target wire : Fin qubits)
    (different : wire ≠ target) (value : Bool) (input : QubitBasis qubits) :
    xorWire target value input wire = input wire := by
  simp [xorWire, different]

/-- XORing the same value into the same wire twice is the identity. -/
theorem xorWire_involutive {qubits : Nat} (target : Fin qubits) (value : Bool) :
    Function.Involutive (xorWire target value) := by
  intro input
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [xorWire]
  · simp [xorWire, equal]

/-- Constant XOR updates on distinct wires commute. -/
theorem xorWire_commute {qubits : Nat} (first second : Fin qubits)
    (different : first ≠ second) (firstValue secondValue : Bool)
    (input : QubitBasis qubits) :
    xorWire first firstValue (xorWire second secondValue input) =
      xorWire second secondValue (xorWire first firstValue input) := by
  funext wire
  by_cases wireFirst : wire = first
  · subst wire
    cases input first <;> cases firstValue <;> cases secondValue <;>
      simp [xorWire, different, Ne.symm different]
  · by_cases wireSecond : wire = second
    · subst wire
      cases input second <;> cases firstValue <;> cases secondValue <;>
        simp [xorWire, different, Ne.symm different]
    · simp [xorWire, wireFirst, wireSecond]

/-- Pauli-X の局所行列。 -/
def localX : Matrix Bool Bool ℂ :=
  fun output input => if output = !input then 1 else 0

/-- Pauli-Z の局所行列。 -/
def localZ : Matrix Bool Bool ℂ :=
  fun output input => if output ≠ input then 0 else if input then -1 else 1

/-- Hadamard の局所行列。 -/
def localH : Matrix Bool Bool ℂ :=
  fun output input =>
    let scale : ℂ := (1 / Real.sqrt 2 : ℝ)
    if output && input then -scale else scale

/-- 一の基底だけへ指定した複素位相を掛ける局所対角行列。 -/
def localPhase (phase : ℂ) : Matrix Bool Bool ℂ :=
  fun output input => if output ≠ input then 0 else if input then phase else 1

/-- A one-qubit phase shift with matrix `diag(1, exp(i * angle))`. -/
def localPhaseShift (angle : ℝ) : Matrix Bool Bool ℂ :=
  localPhase (Complex.exp (Complex.I * (angle : ℂ)))

/-- 位相 gate S の局所行列。 -/
def localS : Matrix Bool Bool ℂ := localPhase Complex.I

/-- 逆位相 gate S† の局所行列。 -/
def localSdg : Matrix Bool Bool ℂ := localPhase (-Complex.I)

/-- 位相 gate T の局所行列。 -/
def localT : Matrix Bool Bool ℂ :=
  localPhase (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)))

/-- 逆位相 gate T† の局所行列。 -/
def localTdg : Matrix Bool Bool ℂ :=
  localPhase (Complex.exp (-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)))

/-- Y 軸回転 `Ry(angle)` の局所行列。 -/
def localRy (angle : ℝ) : Matrix Bool Bool ℂ :=
  fun output input =>
    let cosine : ℂ := Real.cos (angle / 2)
    let sine : ℂ := Real.sin (angle / 2)
    match output, input with
    | false, false => cosine
    | false, true => -sine
    | true, false => sine
    | true, true => cosine

/-- Z 軸回転 `Rz(angle)` の局所行列。 -/
def localRz (angle : ℝ) : Matrix Bool Bool ℂ :=
  fun output input =>
    if output ≠ input then 0
    else if input then
      Complex.exp (Complex.I * (angle / 2 : ℂ))
    else
      Complex.exp (-Complex.I * (angle / 2 : ℂ))

/-- 全基底へ同じ位相を掛ける解析作用素。 -/
def globalPhaseOperator {basis : Type*} [DecidableEq basis]
    (angle : ℝ) : Operator basis :=
  fun output input =>
    if output = input then Complex.exp (Complex.I * angle) else 0

end

end VerifiedCircuitCore
