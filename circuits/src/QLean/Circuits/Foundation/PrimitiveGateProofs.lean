import QLean.Circuits.Foundation.Gates

/-!
# 基本ゲートの合成的なユニタリ意味論

固定一・二量子ビットの局所行列だけを直接検査し、任意幅への埋込みは
Kronecker積、添字同値、置換行列の一般補題で証明する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Reindexing a local operator tensored with the identity preserves
multiplication.  The ambient basis may be any finite type equipped with a
split into local and untouched factors. -/
theorem reindexKroneckerOne_mul
    {basis localBasis outsideBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype localBasis] [DecidableEq localBasis]
    [Fintype outsideBasis] [DecidableEq outsideBasis]
    (split : basis ≃ localBasis × outsideBasis)
    (left right : Operator localBasis) :
    Matrix.reindex split.symm split.symm
        (Matrix.kronecker (left * right) (1 : Operator outsideBasis)) =
      Matrix.reindex split.symm split.symm
          (Matrix.kronecker left (1 : Operator outsideBasis)) *
        Matrix.reindex split.symm split.symm
          (Matrix.kronecker right (1 : Operator outsideBasis)) := by
  calc
    Matrix.reindex split.symm split.symm
        (Matrix.kronecker (left * right) (1 : Operator outsideBasis)) =
      Matrix.reindex split.symm split.symm
        (Matrix.kronecker (left * right)
          ((1 : Operator outsideBasis) * 1)) := by simp
    _ = Matrix.reindex split.symm split.symm
        (Matrix.kronecker left (1 : Operator outsideBasis) *
          Matrix.kronecker right (1 : Operator outsideBasis)) := by
          apply congrArg
          exact Matrix.mul_kronecker_mul left right 1 1
    _ = Matrix.reindex split.symm split.symm
          (Matrix.kronecker left (1 : Operator outsideBasis)) *
        Matrix.reindex split.symm split.symm
          (Matrix.kronecker right (1 : Operator outsideBasis)) :=
      (Matrix.reindexRingEquiv ℂ split.symm).map_mul _ _

/-- 行列の添字を同値で付け替えてもユニタリ性は保存される。 -/
theorem reindex_mem_unitaryGroup
    {oldBasis newBasis : Type*}
    [Fintype oldBasis] [DecidableEq oldBasis]
    [Fintype newBasis] [DecidableEq newBasis]
    (equiv : oldBasis ≃ newBasis)
    {operator : Operator oldBasis}
    (unitary : operator ∈ Matrix.unitaryGroup oldBasis ℂ) :
    Matrix.reindex equiv equiv operator ∈ Matrix.unitaryGroup newBasis ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at unitary ⊢
  change Matrix.reindex equiv equiv operator *
      star (Matrix.reindex equiv equiv operator) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexLinearEquiv ℂ ℂ equiv equiv operator) *
      (Matrix.reindexLinearEquiv ℂ ℂ equiv equiv (star operator)) = 1
  rw [Matrix.reindexLinearEquiv_mul]
  have original : operator * star operator = 1 := unitary
  rw [original]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ equiv

/-- ユニタリな一量子ビット行列を任意wireへ埋め込んでもユニタリである。 -/
theorem embedSingleQubitOperator_mem_unitaryGroup
    {qubits : Nat} (target : Fin qubits) (localOperator : Matrix Bool Bool ℂ)
    (unitary : localOperator ∈ Matrix.unitaryGroup Bool ℂ) :
    embedSingleQubitOperator target localOperator ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ := by
  apply reindex_mem_unitaryGroup (splitWireEquiv target).symm
  exact Matrix.kronecker_mem_unitary unitary (Submonoid.one_mem _)

/-- ユニタリな二量子ビット行列を相異なる任意二wireへ埋め込んでもユニタリである。 -/
theorem embedTwoQubitOperator_mem_unitaryGroup
    {qubits : Nat} (first second : Fin qubits) (different : first ≠ second)
    (localOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (unitary : localOperator ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    embedTwoQubitOperator first second different localOperator ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ := by
  apply reindex_mem_unitaryGroup (splitTwoWiresEquiv first second different).symm
  exact Matrix.kronecker_mem_unitary unitary (Submonoid.one_mem _)

/-- 任意の有限基底上の置換行列はユニタリである。 -/
theorem permMatrix_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis) :
    permutation.permMatrix ℂ ∈ Matrix.unitaryGroup basis ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [show star (permutation.permMatrix ℂ) =
      (permutation⁻¹).permMatrix ℂ by
        simp [Matrix.star_eq_conjTranspose]]
  rw [← Matrix.permMatrix_mul]
  simp

/-- 置換行列を一般作用素の左から掛けると出力添字だけが置換される。 -/
theorem permMatrix_mul_operator_apply
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis) (operator : Operator basis)
    (output input : basis) :
    (permutation.permMatrix ℂ * operator) output input =
      operator (permutation output) input := by
  change Matrix.mulVec (permutation.permMatrix ℂ)
      (fun middle => operator middle input) output = _
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- 一般作用素の右から置換行列を掛けると入力添字だけが逆置換される。 -/
theorem operator_mul_permMatrix_apply
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) (permutation : Equiv.Perm basis)
    (output input : basis) :
    (operator * permutation.permMatrix ℂ) output input =
      operator output (permutation.symm input) := by
  change Matrix.vecMul (fun middle => operator output middle)
      (permutation.permMatrix ℂ) input = _
  rw [Matrix.vecMul_permMatrix]
  rfl

/-- 自己逆置換で作用素を挟むと入出力添字の両方へ同じ置換が作用する。 -/
theorem permMatrix_conjugate_operator_apply
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis)
    (involutive : permutation.symm = permutation)
    (operator : Operator basis) (output input : basis) :
    (permutation.permMatrix ℂ * operator * permutation.permMatrix ℂ)
        output input =
      operator (permutation output) (permutation input) := by
  rw [operator_mul_permMatrix_apply, permMatrix_mul_operator_apply, involutive]

/-- 自己逆な基底関数を置換として束ねる。 -/
def involutiveBasisEquiv {basis : Type*} (action : basis → basis)
    (involutive : Function.Involutive action) : Equiv.Perm basis where
  toFun := action
  invFun := action
  left_inv := involutive
  right_inv := involutive

/-- 自己逆な決定的作用素は対応する置換行列である。 -/
theorem deterministicOperator_eq_permMatrix_of_involutive
    {basis : Type*} [DecidableEq basis]
    (action : basis → basis) (involutive : Function.Involutive action) :
    deterministicOperator action =
      (involutiveBasisEquiv action involutive).permMatrix ℂ := by
  ext output input
  have equivalence : output = action input ↔ action output = input := by
    constructor
    · intro equal
      rw [equal]
      exact involutive input
    · intro equal
      calc
        output = action (action output) := (involutive output).symm
        _ = action input := congrArg action equal
  by_cases forward : output = action input
  · simp [deterministicOperator, involutiveBasisEquiv, forward,
      involutive input]
  · have backward : ¬action output = input := by
      intro equal
      exact forward (equivalence.mpr equal)
    simp [deterministicOperator, involutiveBasisEquiv, forward, backward]

/-- 決定的作用素の実行順積は、基底関数を左からfoldした直接0-1作用素である。 -/
theorem operatorSequence_deterministicOperator
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (actions : List (basis → basis)) :
    operatorSequence (actions.map deterministicOperator) =
      deterministicOperator fun input =>
        actions.foldl (fun state action => action state) input := by
  have actionOnKet : ∀ input,
      applyOperator
          (operatorSequence (actions.map deterministicOperator))
          (basisKet input) =
        basisKet (actions.foldl (fun state action => action state) input) := by
    induction actions with
    | nil =>
        intro input
        simp [operatorSequence, applyOperator]
    | cons first rest inductionHypothesis =>
        intro input
        rw [List.map_cons, operatorSequence, applyOperator_mul,
          applyOperator_deterministicOperator_basisKet]
        simpa using inductionHypothesis (first input)
  ext output input
  calc
    operatorSequence (actions.map deterministicOperator) output input =
        applyOperator
          (operatorSequence (actions.map deterministicOperator))
          (basisKet input) output := by
            rw [applyOperator_basisKet]
    _ = basisKet
        (actions.foldl (fun state action => action state) input) output :=
      congrFun (actionOnKet input) output
    _ = (deterministicOperator fun input =>
        actions.foldl (fun state action => action state) input) output input := rfl

/-- 指定wire以外への制限関数の等式は`agreesExcept`と同値である。 -/
theorem restrictedBasis_eq_iff_agreesExcept
    {qubits : Nat} (target : Fin qubits)
    (output input : QubitBasis qubits) :
    (fun wire : {wire : Fin qubits // wire ≠ target} => output wire.1) =
        (fun wire : {wire : Fin qubits // wire ≠ target} => input wire.1) ↔
      agreesExcept target output input := by
  constructor
  · intro equal wire different
    exact congrFun equal ⟨wire, different⟩
  · intro equal
    funext wire
    exact equal wire.1 wire.2

/-- 有限wire集合上の`agreesExcept`は決定可能である。 -/
instance agreesExceptDecidable
    {qubits : Nat} (target : Fin qubits)
    (output input : QubitBasis qubits) :
    Decidable (agreesExcept target output input) := by
  unfold agreesExcept
  infer_instance

/-- 任意wireへ埋め込んだ一量子ビット作用素の行列要素を局所的に評価する。 -/
theorem embedSingleQubitOperator_apply
    {qubits : Nat} (target : Fin qubits) (localOperator : Matrix Bool Bool ℂ)
    (output input : QubitBasis qubits) :
    embedSingleQubitOperator target localOperator output input =
      if agreesExcept target output input then
        localOperator (output target) (input target)
      else 0 := by
  change
    localOperator (output target) (input target) *
        (if
          (fun wire : {wire : Fin qubits // wire ≠ target} => output wire.1) =
            (fun wire : {wire : Fin qubits // wire ≠ target} => input wire.1)
          then 1 else 0) = _
  by_cases equal : agreesExcept target output input
  · have restricted :=
      (restrictedBasis_eq_iff_agreesExcept target output input).2 equal
    simp [equal, restricted]
  · have restricted :
        (fun wire : {wire : Fin qubits // wire ≠ target} => output wire.1) ≠
          (fun wire : {wire : Fin qubits // wire ≠ target} => input wire.1) := by
      intro restrictedEqual
      exact equal
        ((restrictedBasis_eq_iff_agreesExcept target output input).1 restrictedEqual)
    simp [equal, restricted]

/-- 二 wire 外の制限基底の一致は `agreesExceptTwo` と同値である。 -/
theorem restrictedTwoBasis_eq_iff_agreesExceptTwo
    {qubits : Nat} (first second : Fin qubits)
    (output input : QubitBasis qubits) :
    (fun wire : {wire : Fin qubits // wire ≠ first ∧ wire ≠ second} =>
        output wire.1) =
      (fun wire : {wire : Fin qubits // wire ≠ first ∧ wire ≠ second} =>
        input wire.1) ↔
      agreesExceptTwo first second output input := by
  constructor
  · intro equal wire firstDifferent secondDifferent
    exact congrFun equal ⟨wire, firstDifferent, secondDifferent⟩
  · intro equal
    funext wire
    exact equal wire.1 wire.2.1 wire.2.2

/-- 二 wire 外の一致条件は有限 wire 集合上で決定可能である。 -/
instance agreesExceptTwoDecidable
    {qubits : Nat} (first second : Fin qubits)
    (output input : QubitBasis qubits) :
    Decidable (agreesExceptTwo first second output input) := by
  unfold agreesExceptTwo
  infer_instance

/-- 二量子ビット埋込み作用素の行列要素評価式。 -/
theorem embedTwoQubitOperator_apply
    {qubits : Nat} (first second : Fin qubits) (different : first ≠ second)
    (localOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (output input : QubitBasis qubits) :
    embedTwoQubitOperator first second different localOperator output input =
      if agreesExceptTwo first second output input then
        localOperator (output first, output second) (input first, input second)
      else 0 := by
  change
    localOperator (output first, output second) (input first, input second) *
        (if
          (fun wire : {wire : Fin qubits // wire ≠ first ∧ wire ≠ second} =>
              output wire.1) =
            (fun wire : {wire : Fin qubits // wire ≠ first ∧ wire ≠ second} =>
              input wire.1)
          then 1 else 0) = _
  by_cases equal : agreesExceptTwo first second output input
  · have restricted :=
      (restrictedTwoBasis_eq_iff_agreesExceptTwo first second output input).2 equal
    simp [equal, restricted]
  · have restricted :
        (fun wire : {wire : Fin qubits // wire ≠ first ∧ wire ≠ second} =>
            output wire.1) ≠
          (fun wire : {wire : Fin qubits // wire ≠ first ∧ wire ≠ second} =>
            input wire.1) := by
      intro restrictedEqual
      exact equal
        ((restrictedTwoBasis_eq_iff_agreesExceptTwo first second output input).1
          restrictedEqual)
    simp [equal, restricted]
/-- Pauli-X局所行列はユニタリである。 -/
theorem localX_mem_unitaryGroup :
    localX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext output input
  cases output <;> cases input <;>
    simp [localX, Matrix.mul_apply, Matrix.star_eq_conjTranspose]

/-- Pauli-Z局所行列はユニタリである。 -/
theorem localZ_mem_unitaryGroup :
    localZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext output input
  cases output <;> cases input <;>
    simp [localZ, Matrix.mul_apply, Matrix.star_eq_conjTranspose]

/-- 任意の実角度に対する`Ry`局所行列はユニタリである。 -/
theorem localRy_mem_unitaryGroup (angle : ℝ) :
    localRy angle ∈ Matrix.unitaryGroup Bool ℂ := by
  have sineFixed :
      (starRingEnd ℂ) (Complex.sin ((angle : ℂ) * (1 / 2))) =
        Complex.sin ((angle : ℂ) * (1 / 2)) := by
    rw [← Complex.sin_conj]
    congr 1
    simp
    left
    exact map_ofNat (starRingEnd ℂ) 2
  have cosineFixed :
      (starRingEnd ℂ) (Complex.cos ((angle : ℂ) * (1 / 2))) =
        Complex.cos ((angle : ℂ) * (1 / 2)) := by
    rw [← Complex.cos_conj]
    congr 1
    simp
    left
    exact map_ofNat (starRingEnd ℂ) 2
  rw [Matrix.mem_unitaryGroup_iff]
  ext output input
  cases output <;> cases input <;>
    simp [localRy, Matrix.mul_apply, Matrix.star_eq_conjTranspose] <;>
    ring_nf <;>
    rw [sineFixed, cosineFixed] <;>
    ring_nf
  · exact Complex.sin_sq_add_cos_sq _
  · exact Complex.cos_sq_add_sin_sq _

/-- Hadamard局所行列はユニタリである。 -/
theorem localH_mem_unitaryGroup :
    localH ∈ Matrix.unitaryGroup Bool ℂ := by
  have squareRoot : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have nonzero : Real.sqrt 2 ≠ 0 := by positivity
  have squareRootComplex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (show (Real.sqrt 2) ^ 2 = 2 by rw [pow_two]; exact squareRoot)
  rw [Matrix.mem_unitaryGroup_iff]
  ext output input
  cases output <;> cases input <;>
    simp [localH, Matrix.mul_apply, Matrix.star_eq_conjTranspose] <;>
    field_simp
  all_goals convert squareRootComplex.symm using 1 <;> norm_num

/-- 絶対値一の複素数による局所phase行列はユニタリである。 -/
theorem localPhase_mem_unitaryGroup (phase : ℂ)
    (phaseUnit : phase * star phase = 1) :
    localPhase phase ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext output input
  cases output <;> cases input
  · simp [localPhase, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  · simp [localPhase, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  · simp [localPhase, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  · simpa [localPhase, Matrix.mul_apply, Matrix.star_eq_conjTranspose] using phaseUnit

/-- 純虚数指数の複素phaseは絶対値一である。 -/
theorem complexExp_imaginary_mul_star (angle : ℝ) :
    Complex.exp (Complex.I * (angle : ℂ)) *
      star (Complex.exp (Complex.I * (angle : ℂ))) = 1 := by
  change Complex.exp (Complex.I * (angle : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * (angle : ℂ))) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

/-- A phase-shift local matrix is unitary at every real angle. -/
theorem localPhaseShift_mem_unitaryGroup (angle : ℝ) :
    localPhaseShift angle ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold localPhaseShift
  exact localPhase_mem_unitaryGroup _ (complexExp_imaginary_mul_star angle)

/-- S局所行列はユニタリである。 -/
theorem localS_mem_unitaryGroup :
    localS ∈ Matrix.unitaryGroup Bool ℂ := by
  apply localPhase_mem_unitaryGroup
  norm_num

/-- S随伴局所行列はユニタリである。 -/
theorem localSdg_mem_unitaryGroup :
    localSdg ∈ Matrix.unitaryGroup Bool ℂ := by
  apply localPhase_mem_unitaryGroup
  norm_num

/-- T局所行列はユニタリである。 -/
theorem localT_mem_unitaryGroup :
    localT ∈ Matrix.unitaryGroup Bool ℂ := by
  apply localPhase_mem_unitaryGroup
  exact complexExp_imaginary_mul_star (Real.pi / 4)

/-- T随伴局所行列はユニタリである。 -/
theorem localTdg_mem_unitaryGroup :
    localTdg ∈ Matrix.unitaryGroup Bool ℂ := by
  apply localPhase_mem_unitaryGroup
  have exponent :
      -Complex.I * ((Real.pi / 4 : ℝ) : ℂ) =
        Complex.I * ((-(Real.pi / 4) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [exponent]
  exact complexExp_imaginary_mul_star (-(Real.pi / 4))

/-- 任意の実角度に対する`Rz`局所行列はユニタリである。 -/
theorem localRz_mem_unitaryGroup (angle : ℝ) :
    localRz angle ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext output input
  cases output <;> cases input
  · simp [localRz, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
    have exponent :
        -(Complex.I * ((angle : ℂ) / 2)) =
          Complex.I * ((-(angle / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [exponent]
    exact complexExp_imaginary_mul_star (-(angle / 2))
  · simp [localRz, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  · simp [localRz, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  · simp [localRz, Matrix.mul_apply, Matrix.star_eq_conjTranspose]
    convert complexExp_imaginary_mul_star (angle / 2) using 1
    all_goals
      simp only [starRingEnd_apply]
      push_cast
      ring_nf

/-- 局所ユニタリをcontrol bitが一の部分だけへ適用してもユニタリである。 -/
theorem localControlledOperator_mem_unitaryGroup
    (localOperator : Matrix Bool Bool ℂ)
    (unitary : localOperator ∈ Matrix.unitaryGroup Bool ℂ) :
    localControlledOperator localOperator ∈
      Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at unitary ⊢
  have unitaryEntry (output input : Bool) :
      ∑ middle : Bool,
          localOperator output middle * star (localOperator input middle) =
        if output = input then 1 else 0 := by
    have entry := congrFun (congrFun unitary output) input
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.one_apply] using entry
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases inputControl
  · by_cases targetsEqual : outputTarget = inputTarget
    · subst outputTarget
      simp [localControlledOperator, Matrix.mul_apply,
        Matrix.star_eq_conjTranspose,
        Fintype.sum_prod_type]
    · simp [localControlledOperator, Matrix.mul_apply,
        Matrix.star_eq_conjTranspose,
        Fintype.sum_prod_type, targetsEqual, Ne.symm targetsEqual]
  · simp [localControlledOperator, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose,
      Fintype.sum_prod_type]
  · simp [localControlledOperator, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose,
      Fintype.sum_prod_type]
  · simpa [localControlledOperator, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.one_apply,
      Fintype.sum_prod_type] using
      unitaryEntry outputTarget inputTarget

/-- ユニタリな局所行列の制御付き任意wire埋込みはユニタリである。 -/
theorem embedControlledSingleQubitOperator_mem_unitaryGroup
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ)
    (unitary : localOperator ∈ Matrix.unitaryGroup Bool ℂ) :
    embedControlledSingleQubitOperator control target different localOperator ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ :=
  embedTwoQubitOperator_mem_unitaryGroup control target different _
    (localControlledOperator_mem_unitaryGroup localOperator unitary)

/-- Global phase作用素は絶対値一のscalarとidentity作用素の積である。 -/
theorem globalPhaseOperator_eq_smul_one
    {basis : Type*} [DecidableEq basis] (angle : ℝ) :
    globalPhaseOperator angle =
      Complex.exp (Complex.I * angle) • (1 : Operator basis) := by
  ext output input
  by_cases equal : output = input
  · subst output
    simp [globalPhaseOperator]
  · simp [globalPhaseOperator, equal]

/-- 任意の実角度によるglobal phase作用素は行列代数上ユニタリである。 -/
theorem globalPhaseOperator_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis] (angle : ℝ) :
    globalPhaseOperator angle ∈ Matrix.unitaryGroup basis ℂ := by
  rw [globalPhaseOperator_eq_smul_one]
  rw [Matrix.mem_unitaryGroup_iff]
  have phaseUnit := complexExp_imaginary_mul_star angle
  have phaseUnitReversed :
      star (Complex.exp (Complex.I * (angle : ℂ))) *
        Complex.exp (Complex.I * (angle : ℂ)) = 1 := by
    rw [mul_comm]
    exact phaseUnit
  simp only [star_smul, star_one, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    phaseUnitReversed, one_smul]

/-- 自己逆関数では`output = f input`と`f output = input`が同値である。 -/
theorem eq_action_iff_action_eq_of_involutive
    {basis : Type*} (action : basis → basis)
    (involutive : ∀ input, action (action input) = input)
    (output input : basis) :
    output = action input ↔ action output = input := by
  constructor
  · intro equal
    rw [equal]
    exact involutive input
  · intro equal
    have mapped := congrArg action equal
    simpa only [involutive] using mapped

/-- CNOTの回路非依存な計算基底作用。 -/
def cnotBasisAction {qubits : Nat} (control target : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire target (input control) input

/-- 相異なるcontrol/target上のCNOT基底作用は自己逆である。 -/
theorem cnotBasisAction_involutive
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (input : QubitBasis qubits) :
    cnotBasisAction control target (cnotBasisAction control target input) = input := by
  funext wire
  by_cases isTarget : wire = target
  · subst wire
    simp [cnotBasisAction, xorWire, different]
  · simp [cnotBasisAction, xorWire, different, isTarget]

/-- CNOTの基底作用を自己逆な置換として束ねる。 -/
def cnotBasisEquiv {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) : Equiv.Perm (QubitBasis qubits) where
  toFun := cnotBasisAction control target
  invFun := cnotBasisAction control target
  left_inv := cnotBasisAction_involutive control target different
  right_inv := cnotBasisAction_involutive control target different

/-- Toffoliの回路非依存な計算基底作用。 -/
def toffoliBasisAction {qubits : Nat}
    (control₁ control₂ target : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire target (input control₁ && input control₂) input

/-- targetが両controlと異なるToffoli基底作用は自己逆である。 -/
theorem toffoliBasisAction_involutive
    {qubits : Nat} (control₁ control₂ target : Fin qubits)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (input : QubitBasis qubits) :
    toffoliBasisAction control₁ control₂ target
        (toffoliBasisAction control₁ control₂ target input) = input := by
  funext wire
  by_cases isTarget : wire = target
  · subst wire
    simp [toffoliBasisAction, xorWire, firstDifferent, secondDifferent]
  · simp [toffoliBasisAction, xorWire, firstDifferent, secondDifferent, isTarget]

/-- Toffoliの基底作用を自己逆な置換として束ねる。 -/
def toffoliBasisEquiv {qubits : Nat}
    (control₁ control₂ target : Fin qubits)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) : Equiv.Perm (QubitBasis qubits) where
  toFun := toffoliBasisAction control₁ control₂ target
  invFun := toffoliBasisAction control₁ control₂ target
  left_inv := toffoliBasisAction_involutive control₁ control₂ target
    firstDifferent secondDifferent
  right_inv := toffoliBasisAction_involutive control₁ control₂ target
    firstDifferent secondDifferent

/-- CNOTの決定的作用素は対応する基底置換行列である。 -/
theorem deterministicOperator_cnotBasisAction_eq_permMatrix
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target) :
  deterministicOperator (cnotBasisAction control target) =
      (cnotBasisEquiv control target different).permMatrix ℂ := by
  ext output input
  have equivalence := eq_action_iff_action_eq_of_involutive
    (cnotBasisAction control target)
    (cnotBasisAction_involutive control target different) output input
  by_cases forward : output = cnotBasisAction control target input
  · simp [deterministicOperator, cnotBasisEquiv, forward]
    exact cnotBasisAction_involutive control target different input
  · have backward : ¬cnotBasisAction control target output = input := by
      intro equal
      exact forward (equivalence.mpr equal)
    simp [deterministicOperator, cnotBasisEquiv, forward, backward]

/-- Toffoliの決定的作用素は対応する基底置換行列である。 -/
theorem deterministicOperator_toffoliBasisAction_eq_permMatrix
    {qubits : Nat} (control₁ control₂ target : Fin qubits)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) :
    deterministicOperator (toffoliBasisAction control₁ control₂ target) =
      (toffoliBasisEquiv control₁ control₂ target firstDifferent
        secondDifferent).permMatrix ℂ := by
  ext output input
  have equivalence := eq_action_iff_action_eq_of_involutive
    (toffoliBasisAction control₁ control₂ target)
    (toffoliBasisAction_involutive control₁ control₂ target firstDifferent
      secondDifferent) output input
  by_cases forward : output =
      toffoliBasisAction control₁ control₂ target input
  · simp [deterministicOperator, toffoliBasisEquiv, forward]
    exact toffoliBasisAction_involutive control₁ control₂ target
      firstDifferent secondDifferent input
  · have backward :
        ¬toffoliBasisAction control₁ control₂ target output = input := by
      intro equal
      exact forward (equivalence.mpr equal)
    simp [deterministicOperator, toffoliBasisEquiv, forward, backward]

/-- 全種類の型安全な基本ゲートは任意幅でユニタリな行列意味論を持つ。 -/
theorem primitiveGateOperatorWithSymbols_mem_unitaryGroup
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits) :
    primitiveGateOperatorWithSymbols symbolValue gate ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ := by
  cases gate with
  | x target =>
      exact embedSingleQubitOperator_mem_unitaryGroup target localX
        localX_mem_unitaryGroup
  | h target =>
      exact embedSingleQubitOperator_mem_unitaryGroup target localH
        localH_mem_unitaryGroup
  | ry angle target =>
      exact embedSingleQubitOperator_mem_unitaryGroup target
        (localRy (angle.eval symbolValue))
        (localRy_mem_unitaryGroup (angle.eval symbolValue))
  | phaseShift angle target =>
      exact embedSingleQubitOperator_mem_unitaryGroup target
        (localPhaseShift (angle.eval symbolValue))
        (localPhaseShift_mem_unitaryGroup (angle.eval symbolValue))
  | cnot control target different =>
      change deterministicOperator (cnotBasisAction control target) ∈
        Matrix.unitaryGroup (QubitBasis qubits) ℂ
      rw [deterministicOperator_cnotBasisAction_eq_permMatrix control target different]
      exact permMatrix_mem_unitaryGroup (cnotBasisEquiv control target different)
  | toffoli control₁ control₂ target _ firstDifferent secondDifferent =>
      change deterministicOperator
          (toffoliBasisAction control₁ control₂ target) ∈
        Matrix.unitaryGroup (QubitBasis qubits) ℂ
      rw [deterministicOperator_toffoliBasisAction_eq_permMatrix control₁ control₂
        target firstDifferent secondDifferent]
      exact permMatrix_mem_unitaryGroup
        (toffoliBasisEquiv control₁ control₂ target firstDifferent secondDifferent)

/-- Backward-compatible internal theorem name for the symbol-environment
semantics.  The canonical public operator itself has no environment. -/
theorem primitiveGateOperator_mem_unitaryGroup
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits) :
    primitiveGateOperatorWithSymbols symbolValue gate ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ :=
  primitiveGateOperatorWithSymbols_mem_unitaryGroup symbolValue gate

/-- 基本ゲート列からなる任意回路の理想作用素はユニタリである。 -/
theorem primitiveCircuit_denote_mem_unitaryGroup
    {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ :=
  Circuit.denote_mem_unitaryGroup (primitiveGateOperatorWithSymbols symbolValue)
    (primitiveGateOperatorWithSymbols_mem_unitaryGroup symbolValue) circuit

/-- 一量子ビット埋込みの随伴は局所行列の随伴を埋め込んだものに等しい。 -/
theorem star_embedSingleQubitOperator
    {qubits : Nat} (target : Fin qubits) (localOperator : Matrix Bool Bool ℂ) :
    star (embedSingleQubitOperator target localOperator) =
      embedSingleQubitOperator target (star localOperator) := by
  simp [embedSingleQubitOperator, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker]

/-- 二量子ビット埋込みの随伴は局所行列の随伴を埋め込んだものに等しい。 -/
theorem star_embedTwoQubitOperator
    {qubits : Nat} (first second : Fin qubits) (different : first ≠ second)
    (localOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    star (embedTwoQubitOperator first second different localOperator) =
      embedTwoQubitOperator first second different (star localOperator) := by
  simp [embedTwoQubitOperator, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker]

/-- Pauli-X局所行列は自己随伴である。 -/
theorem star_localX : star localX = localX := by
  ext output input
  cases output <;> cases input <;>
    simp [localX]

/-- Pauli-Z局所行列は自己随伴である。 -/
theorem star_localZ : star localZ = localZ := by
  ext output input
  cases output <;> cases input <;>
    simp [localZ]

/-- Hadamard局所行列は自己随伴である。 -/
theorem star_localH : star localH = localH := by
  ext output input
  cases output <;> cases input <;>
    simp [localH]

/-- 局所phase行列の随伴はphaseを共役した局所phase行列である。 -/
theorem star_localPhase (phase : ℂ) :
    star (localPhase phase) = localPhase (star phase) := by
  ext output input
  cases output <;> cases input <;>
    simp [localPhase]

/-- S局所行列の随伴はS随伴局所行列である。 -/
theorem star_localS : star localS = localSdg := by
  rw [show localS = localPhase Complex.I by rfl, star_localPhase]
  simp [localSdg]

/-- S随伴局所行列の随伴はS局所行列である。 -/
theorem star_localSdg : star localSdg = localS := by
  rw [show localSdg = localPhase (-Complex.I) by rfl, star_localPhase]
  simp [localS]

/-- Ry局所行列の随伴は角度の符号を反転したRyである。 -/
theorem star_localRy (angle : ℝ) :
    star (localRy angle) = localRy (-angle) := by
  have sineFixed :
      (starRingEnd ℂ) (Complex.sin ((angle : ℂ) / 2)) =
        Complex.sin ((angle : ℂ) / 2) := by
    rw [← Complex.sin_conj]
    congr 1
    simp [map_ofNat]
  have cosineFixed :
      (starRingEnd ℂ) (Complex.cos ((angle : ℂ) / 2)) =
        Complex.cos ((angle : ℂ) / 2) := by
    rw [← Complex.cos_conj]
    congr 1
    simp [map_ofNat]
  have negativeHalfComplex : -(angle : ℂ) / 2 =
      -((angle : ℂ) / 2) := by
    ring
  ext output input
  cases output <;> cases input
  · simpa [localRy, negativeHalfComplex, Complex.cos_neg] using cosineFixed
  · simpa [localRy, negativeHalfComplex, Complex.sin_neg] using sineFixed
  · have negativeSineFixed := congrArg Neg.neg sineFixed
    simpa [localRy, negativeHalfComplex, Complex.sin_neg] using negativeSineFixed
  · simpa [localRy, negativeHalfComplex, Complex.cos_neg] using cosineFixed

/-- Rz局所行列の随伴は角度の符号を反転したRzである。 -/
theorem star_localRz (angle : ℝ) :
    star (localRz angle) = localRz (-angle) := by
  ext output input
  cases output <;> cases input <;>
    simp [localRz, ← Complex.exp_conj, map_ofNat] <;>
    congr 1 <;> ring_nf

/-- 純虚数指数phaseの共役は角度の符号を反転したphaseである。 -/
theorem star_complexExp_imaginary (angle : ℝ) :
    star (Complex.exp (Complex.I * (angle : ℂ))) =
      Complex.exp (Complex.I * ((-angle : ℝ) : ℂ)) := by
  change (starRingEnd ℂ) (Complex.exp (Complex.I * (angle : ℂ))) = _
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The adjoint of a phase shift negates its angle. -/
theorem star_localPhaseShift (angle : ℝ) :
    star (localPhaseShift angle) = localPhaseShift (-angle) := by
  unfold localPhaseShift
  rw [star_localPhase, star_complexExp_imaginary]

/-- T局所行列の随伴はT随伴局所行列である。 -/
theorem star_localT : star localT = localTdg := by
  rw [show localT = localPhase
      (Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ))) by rfl,
    star_localPhase]
  unfold localTdg
  congr 1
  rw [star_complexExp_imaginary (Real.pi / 4)]
  congr 1
  push_cast
  ring

/-- T随伴局所行列の随伴はT局所行列である。 -/
theorem star_localTdg : star localTdg = localT := by
  have twice := congrArg star star_localT
  have reversed : localT = star localTdg := by
    simpa using twice
  exact reversed.symm

/-- 制御付き局所行列の随伴は局所行列の随伴を制御したものに等しい。 -/
theorem star_localControlledOperator (localOperator : Matrix Bool Bool ℂ) :
    star (localControlledOperator localOperator) =
      localControlledOperator (star localOperator) := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localControlledOperator]

/-- Global phase作用素の随伴は角度の符号を反転したglobal phaseである。 -/
theorem star_globalPhaseOperator
    {basis : Type*} [DecidableEq basis] (angle : ℝ) :
    star (globalPhaseOperator (basis := basis) angle) =
      globalPhaseOperator (-angle) := by
  ext output input
  by_cases equal : output = input
  · subst output
    simp [globalPhaseOperator, ← Complex.exp_conj]
  · simp [globalPhaseOperator, equal, Ne.symm equal]

/-- 自己逆な基底作用の決定的作用素は自己随伴である。 -/
theorem star_deterministicOperator_of_involutive
    {basis : Type*} [DecidableEq basis]
    (action : basis → basis)
    (involutive : ∀ input, action (action input) = input) :
    star (deterministicOperator action) = deterministicOperator action := by
  ext output input
  have equivalence := eq_action_iff_action_eq_of_involutive action involutive
    output input
  by_cases forward : output = action input
  · simp [deterministicOperator, forward]
    exact (involutive input).symm
  · have backward : ¬action output = input := by
      intro equal
      exact forward (equivalence.mpr equal)
    simp [deterministicOperator, forward]
    exact Ne.symm backward

/-- CNOTの理想作用素は自己随伴である。 -/
theorem star_cnotOperator
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target) :
    star (deterministicOperator (cnotBasisAction control target)) =
      deterministicOperator (cnotBasisAction control target) :=
  star_deterministicOperator_of_involutive (cnotBasisAction control target)
    (cnotBasisAction_involutive control target different)

/-- Toffoliの理想作用素は自己随伴である。 -/
theorem star_toffoliOperator
    {qubits : Nat} (control₁ control₂ target : Fin qubits)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) :
    star (deterministicOperator
        (toffoliBasisAction control₁ control₂ target)) =
      deterministicOperator (toffoliBasisAction control₁ control₂ target) :=
  star_deterministicOperator_of_involutive
    (toffoliBasisAction control₁ control₂ target)
    (toffoliBasisAction_involutive control₁ control₂ target firstDifferent
      secondDifferent)

/-- 制御付き一量子ビット埋込みの随伴は局所随伴を埋め込んだものに等しい。 -/
theorem star_embedControlledSingleQubitOperator
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) :
    star (embedControlledSingleQubitOperator control target different
      localOperator) =
      embedControlledSingleQubitOperator control target different
        (star localOperator) := by
  rw [show embedControlledSingleQubitOperator control target different
      localOperator = embedTwoQubitOperator control target different
        (localControlledOperator localOperator) by rfl,
    star_embedTwoQubitOperator, star_localControlledOperator]
  rfl

/-- 構文的逆基本ゲートの理想作用素は元ゲート作用素の随伴に厳密に等しい。 -/
theorem primitiveGateOperatorWithSymbols_inverse
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits) :
    primitiveGateOperatorWithSymbols symbolValue gate.inverse =
      star (primitiveGateOperatorWithSymbols symbolValue gate) := by
  cases gate with
  | x target =>
      simp [PrimitiveGate.inverse, primitiveGateOperatorWithSymbols,
        star_embedSingleQubitOperator, star_localX]
  | h target =>
      simp [PrimitiveGate.inverse, primitiveGateOperatorWithSymbols,
        star_embedSingleQubitOperator, star_localH]
  | ry angle target =>
      simp [PrimitiveGate.inverse, primitiveGateOperatorWithSymbols,
        star_embedSingleQubitOperator, star_localRy]
  | phaseShift angle target =>
      simp [PrimitiveGate.inverse, primitiveGateOperatorWithSymbols,
        star_embedSingleQubitOperator, star_localPhaseShift]
  | cnot control target different =>
      change deterministicOperator (cnotBasisAction control target) =
        star (deterministicOperator (cnotBasisAction control target))
      exact (star_cnotOperator control target different).symm
  | toffoli control₁ control₂ target _ firstDifferent secondDifferent =>
      change deterministicOperator
          (toffoliBasisAction control₁ control₂ target) =
        star (deterministicOperator
          (toffoliBasisAction control₁ control₂ target))
      exact (star_toffoliOperator control₁ control₂ target firstDifferent
        secondDifferent).symm

/-- Backward-compatible internal inverse theorem for the symbol-environment
semantics. -/
theorem primitiveGateOperator_inverse
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits) :
    primitiveGateOperatorWithSymbols symbolValue gate.inverse =
      star (primitiveGateOperatorWithSymbols symbolValue gate) :=
  primitiveGateOperatorWithSymbols_inverse symbolValue gate

/-- 回路構文木の逆実行は理想作用素の随伴に厳密に等しい。 -/
theorem primitiveCircuit_denote_reverse
    {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (circuit.reverse PrimitiveGate.inverse) =
      star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit) := by
  exact Circuit.denote_reverse PrimitiveGate.inverse
    (primitiveGateOperatorWithSymbols symbolValue)
    (primitiveGateOperatorWithSymbols_inverse symbolValue) circuit

end

end VerifiedCircuitCore
