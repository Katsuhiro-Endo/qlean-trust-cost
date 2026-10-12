import QLean.Generator.Implementation.QuantumSemanticsCorrectness

/-!
# 二量子ビット局所作用の任意幅への持上げ

相異なる二本のwireと残りのwireを同値写像で分離し、固定4次元で証明した
controlled-`Ry`恒等式を任意幅へ持ち上げる。全体基底の列挙は行わない。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 二本の指定wire以外のwire型。 -/
abbrev OutsideTwoWires
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits) :=
  {wire : Wire ancillaQubits systemQubits // wire ≠ first ∧ wire ≠ second}

/-- 二本の指定wire以外に値を割り当てる計算基底。 -/
abbrev OutsideTwoBasis
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits) :=
  OutsideTwoWires first second → Bool

/-- 相異なる二本のwireと、それ以外の全wireへ計算基底を分解する同値。 -/
def splitTwoWiresEquiv
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (different : first ≠ second) :
    JointBasis ancillaQubits systemQubits ≃
      (Bool × Bool) × (OutsideTwoWires first second → Bool) where
  toFun basis := ((basis first, basis second), fun wire => basis wire.1)
  invFun pair := fun wire =>
    if equalFirst : wire = first then pair.1.1
    else if equalSecond : wire = second then pair.1.2
    else pair.2 ⟨wire, equalFirst, equalSecond⟩
  left_inv basis := by
    funext wire
    by_cases equalFirst : wire = first
    · subst wire
      simp
    · by_cases equalSecond : wire = second
      · subst wire
        simp [equalFirst]
      · simp [equalFirst, equalSecond]
  right_inv pair := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [different.symm]
    · funext wire
      simp [wire.2.1, wire.2.2]

/-- 固定二量子ビット作用素を指定した二本のwireへ埋め込む。 -/
def onTwoWires
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (different : first ≠ second)
    (operator : Operator (Bool × Bool)) :
    Operator (JointBasis ancillaQubits systemQubits) :=
  Matrix.reindex (splitTwoWiresEquiv first second different).symm
    (splitTwoWiresEquiv first second different).symm
    (Matrix.kronecker operator
      (1 : Operator (OutsideTwoBasis first second)))

/-- 二wire局所作用の埋込みは行列積を保存する。 -/
theorem onTwoWires_mul
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (different : first ≠ second)
    (left right : Operator (Bool × Bool)) :
    onTwoWires first second different (left * right) =
      onTwoWires first second different left *
        onTwoWires first second different right := by
  exact VerifiedCircuitCore.reindexKroneckerOne_mul
    (splitTwoWiresEquiv first second different) left right

/-- 二つの基底が指定した二本以外の全wireで一致するという条件。 -/
def SameOutsideTwo
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) : Prop :=
  ∀ wire, wire ≠ first → wire ≠ second → output wire = input wire

/-- 有限個のwireに対する`SameOutsideTwo`は決定可能である。 -/
instance sameOutsideTwoDecidable
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) :
    Decidable (SameOutsideTwo first second output input) := by
  unfold SameOutsideTwo
  infer_instance

/-- 二wire外側の制限関数の等式は`SameOutsideTwo`と同値である。 -/
theorem restrictedTwoBasis_eq_iff_sameOutsideTwo
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) :
    (fun wire : OutsideTwoWires first second => output wire.1) =
        (fun wire : OutsideTwoWires first second => input wire.1) ↔
      SameOutsideTwo first second output input := by
  constructor
  · intro equal wire firstDifferent secondDifferent
    exact congrFun equal ⟨wire, firstDifferent, secondDifferent⟩
  · intro equal
    funext wire
    exact equal wire.1 wire.2.1 wire.2.2

/-- 任意幅へ埋め込んだ二量子ビット作用素の行列要素を局所的に評価する。 -/
theorem onTwoWires_apply
    {ancillaQubits systemQubits : Nat}
    (first second : Wire ancillaQubits systemQubits)
    (different : first ≠ second)
    (operator : Operator (Bool × Bool))
    (output input : JointBasis ancillaQubits systemQubits) :
    onTwoWires first second different operator output input =
      if SameOutsideTwo first second output input then
        operator (output first, output second) (input first, input second)
      else 0 := by
  change
    operator (output first, output second) (input first, input second) *
        (if
          (fun wire : OutsideTwoWires first second => output wire.1) =
            (fun wire : OutsideTwoWires first second => input wire.1)
          then 1 else 0) = _
  by_cases equal : SameOutsideTwo first second output input
  · have restricted :=
      (restrictedTwoBasis_eq_iff_sameOutsideTwo first second output input).2 equal
    simp [equal, restricted]
  · have restricted :
        (fun wire : OutsideTwoWires first second => output wire.1) ≠
          (fun wire : OutsideTwoWires first second => input wire.1) := by
      exact fun contradiction => equal
        ((restrictedTwoBasis_eq_iff_sameOutsideTwo first second output input).1
          contradiction)
    simp [equal, restricted]

/-- targetへの一量子ビット作用は、任意の別wireを第一成分にした二wire埋込みと一致する。 -/
theorem onWire_eq_onTwoWires_localTarget
    {ancillaQubits systemQubits : Nat}
    (first target : Wire ancillaQubits systemQubits)
    (different : first ≠ target)
    (operator : Operator Bool) :
    onWire target operator =
      onTwoWires first target different (localTargetMatrix operator) := by
  ext output input
  rw [onWire_apply, onTwoWires_apply]
  by_cases sameTarget : SameOutside target output input
  · have firstEqual : output first = input first :=
      sameTarget first different
    have sameTwo : SameOutsideTwo first target output input := by
      intro wire _ targetDifferent
      exact sameTarget wire targetDifferent
    simp [sameTarget, sameTwo, localTargetMatrix, firstEqual]
  · by_cases firstEqual : output first = input first
    · have notSameTwo : ¬SameOutsideTwo first target output input := by
        intro sameTwo
        apply sameTarget
        intro wire targetDifferent
        by_cases isFirst : wire = first
        · subst wire
          exact firstEqual
        · exact sameTwo wire isFirst targetDifferent
      simp [sameTarget, notSameTwo]
    · simp [sameTarget, localTargetMatrix, firstEqual]

/-- CNOTの全体基底作用は二wire局所条件と外側不変条件に分解できる。 -/
theorem eq_cnotBasisAction_iff_local
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (output input : JointBasis ancillaQubits systemQubits) :
    output = cnotBasisAction control target input ↔
      SameOutsideTwo control target output input ∧
        output control = input control ∧
        output target = if input control then !(input target) else input target := by
  constructor
  · intro equal
    subst output
    refine ⟨?_, ?_, ?_⟩
    · intro wire _ targetDifferent
      simp [cnotBasisAction, targetDifferent]
    · simp [cnotBasisAction, different]
    · simp [cnotBasisAction]
  · rintro ⟨sameOutside, controlEqual, targetEqual⟩
    funext wire
    by_cases isTarget : wire = target
    · subst wire
      simpa [cnotBasisAction] using targetEqual
    · by_cases isControl : wire = control
      · subst wire
        simpa [cnotBasisAction, different] using controlEqual
      · simpa [cnotBasisAction, isTarget] using
          sameOutside wire isControl isTarget

/-- CNOT置換行列の要素は、その一意な基底作用先でのみ1になる。 -/
theorem cnotMatrix_apply_sparse
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (output input : JointBasis ancillaQubits systemQubits) :
    cnotMatrix control target different output input =
      if output = cnotBasisAction control target input then 1 else 0 := by
  let circuit : Circuit (ReversibleGate ancillaQubits systemQubits) :=
    .gate (.cnot control target different)
  have amplitude := reversibleCircuit_basisAmplitude circuit input output
  simpa [circuit, ReversibleCircuit.toPrimitive, Circuit.map,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.denote, ReversibleGate.toPrimitive,
    primitiveGateOperator] using amplitude

/-- 任意幅のCNOTは固定二量子ビットCNOT行列の二wire埋込みに一致する。 -/
theorem cnotMatrix_eq_onTwoWires_localCnot
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) :
    cnotMatrix control target different =
      onTwoWires control target different localCnotMatrix := by
  ext output input
  rw [cnotMatrix_apply_sparse, onTwoWires_apply]
  simp only [eq_cnotBasisAction_iff_local control target different output input]
  by_cases sameOutside : SameOutsideTwo control target output input
  · by_cases controlEqual : output control = input control
    · simp [sameOutside, controlEqual, localCnotMatrix]
    · simp [sameOutside, controlEqual, localCnotMatrix]
  · simp [sameOutside]

/-- 基本ゲート分解した1-control `Ry`は任意幅で理想controlled-`Ry`に一致する。 -/
theorem controlledRyCircuit_operator
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (angle : AngleExpr) :
    (controlledRyCircuit control target different angle).toIdealOperator
        primitiveGateOperator =
      onTwoWires control target different
        (localControlledRyMatrix angle.toReal) := by
  simp only [controlledRyCircuit, Circuit.fromList,
    VerifiedCircuitCore.Circuit.fromList,
    VerifiedCircuitCore.Circuit.denote,
    primitiveGateOperator, Matrix.one_mul]
  rw [AngleExpr.toReal_half, AngleExpr.toReal_neg,
    AngleExpr.toReal_half]
  rw [onWire_eq_onTwoWires_localTarget control target different]
  rw [onWire_eq_onTwoWires_localTarget control target different]
  rw [cnotMatrix_eq_onTwoWires_localCnot control target different]
  have localEquality := local_controlledRy_decomposition angle.toReal
  calc
    onTwoWires control target different localCnotMatrix *
          onTwoWires control target different
            (localTargetMatrix (ryMatrix (-(angle.toReal / 2)))) *
        onTwoWires control target different localCnotMatrix *
      onTwoWires control target different
        (localTargetMatrix (ryMatrix (angle.toReal / 2))) =
      onTwoWires control target different
        (localCnotMatrix *
          localTargetMatrix (ryMatrix (-(angle.toReal / 2))) *
          localCnotMatrix *
          localTargetMatrix (ryMatrix (angle.toReal / 2))) := by
            rw [onTwoWires_mul, onTwoWires_mul, onTwoWires_mul]
    _ = onTwoWires control target different
        (localControlledRyMatrix angle.toReal) := by
      have negHalf : -(angle.toReal / 2) = -angle.toReal / 2 := by ring
      rw [negHalf, localEquality]

/-- target以外の一致は、二wire外側の一致とcontrol値の一致へ分解できる。 -/
theorem sameOutside_iff_sameOutsideTwo_and_control
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (output input : JointBasis ancillaQubits systemQubits) :
    SameOutside target output input ↔
      SameOutsideTwo control target output input ∧
        output control = input control := by
  constructor
  · intro sameTarget
    exact ⟨fun wire _ targetDifferent => sameTarget wire targetDifferent,
      sameTarget control different⟩
  · rintro ⟨sameTwo, controlEqual⟩ wire targetDifferent
    by_cases isControl : wire = control
    · subst wire
      exact controlEqual
    · exact sameTwo wire isControl targetDifferent

/-- 1-control `Ry`回路の行列要素はtargetの二項だけを持つ疎な局所式になる。 -/
theorem controlledRyCircuit_apply_sparse
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (angle : AngleExpr)
    (output input : JointBasis ancillaQubits systemQubits) :
    (controlledRyCircuit control target different angle).toIdealOperator
        primitiveGateOperator output input =
      if SameOutside target output input then
        if input control then
          ryMatrix angle.toReal (output target) (input target)
        else if output target = input target then 1 else 0
      else 0 := by
  rw [controlledRyCircuit_operator]
  rw [onTwoWires_apply]
  simp only [sameOutside_iff_sameOutsideTwo_and_control control target different]
  by_cases sameTwo : SameOutsideTwo control target output input
  · by_cases controlEqual : output control = input control
    · simp [sameTwo, controlEqual, localControlledRyMatrix]
    · simp [sameTwo, controlEqual, localControlledRyMatrix]
  · simp [sameTwo]

end

end ProbabilityGeneratorQProof
