import QLean.Generator.Implementation.TwoWireSemantics

/-!
# 振幅判定回路の疎な意味論

`H-CNOT-H` の計算は固定二量子ビットの局所恒等式として一度だけ証明し、
任意幅のレジスタ上では置換行列との合成として扱う。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 制御ビットと標的ビットがともに1のときだけ符号を反転する局所CZ行列。 -/
def localControlledZMatrix : Operator (Bool × Bool) :=
  Matrix.of fun output input =>
    if output = input then
      if input.1 && input.2 then -1 else 1
    else 0

/-- HadamardでCNOTの標的を挟むと局所CZ行列になる。 -/
theorem local_h_cnot_h :
    localTargetMatrix hMatrix *
        (localCnotMatrix * localTargetMatrix hMatrix) =
      localControlledZMatrix := by
  have coefficientSq : ((hadamardCoefficient : ℂ) ^ 2) = 1 / 2 := by
    calc
      ((hadamardCoefficient : ℂ) ^ 2) =
          ((hadamardCoefficient ^ 2 : ℝ) : ℂ) := by norm_num
      _ = (((1 : ℝ) / 2 : ℝ) : ℂ) :=
        congrArg (λ value : ℝ => (value : ℂ)) hadamardCoefficient_sq
      _ = 1 / 2 := by norm_num
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fintype.sum_prod_type] <;>
    simp [localTargetMatrix, localCnotMatrix, localControlledZMatrix,
      hMatrix] <;>
    ring_nf <;>
    rw [coefficientSq] <;>
    norm_num

/-- 任意幅へ埋め込んだ`H-CNOT-H`も、対応する二wire上のCZに等しい。 -/
theorem embedded_h_cnot_h
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) :
    onWire target hMatrix *
        (cnotMatrix control target different * onWire target hMatrix) =
      onTwoWires control target different localControlledZMatrix := by
  rw [onWire_eq_onTwoWires_localTarget control target different]
  rw [cnotMatrix_eq_onTwoWires_localCnot control target different]
  rw [← onTwoWires_mul, ← onTwoWires_mul]
  rw [local_h_cnot_h]

/-- 振幅判定回路の作用素はCZとactive制御CNOTの積へ簡約できる。 -/
theorem copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_operator (p : QParameters) :
    (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator primitiveGateOperator =
      onTwoWires (negativeWire p) (amplitudeSignalWire p)
          (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix *
        cnotMatrix (activeWire p) (amplitudeSignalWire p)
          (activeWire_ne_amplitudeSignalWire p) := by
  simp only [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit, Circuit.fromList,
    VerifiedCircuitCore.Circuit.fromList,
    VerifiedCircuitCore.Circuit.denote, primitiveGateOperator, Matrix.one_mul]
  rw [Matrix.mul_assoc
    (onWire (amplitudeSignalWire p) hMatrix)
    (cnotMatrix (negativeWire p) (amplitudeSignalWire p)
      (negativeWire_ne_amplitudeSignalWire p))
    (onWire (amplitudeSignalWire p) hMatrix)]
  rw [embedded_h_cnot_h (negativeWire p) (amplitudeSignalWire p)
    (negativeWire_ne_amplitudeSignalWire p)]

/-- CNOT後もその制御wire以外の任意wire値は、標的でない限り保存される。 -/
theorem cnotBasisAction_control_or_other
    {ancillaQubits systemQubits : Nat}
    (control target wire : Wire ancillaQubits systemQubits)
    (targetDifferent : wire ≠ target)
    (input : JointBasis ancillaQubits systemQubits) :
    cnotBasisAction control target input wire = input wire := by
  simp [cnotBasisAction, targetDifferent]

/-- 振幅判定回路はactiveを信号wireへXORし、negativeとの積に応じた位相だけを付ける。 -/
theorem copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_apply_sparse
    (p : QParameters)
    (output input : JointBasis p.ancillaWidth p.systemWidth) :
    (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator primitiveGateOperator
        output input =
      if output = cnotBasisAction (activeWire p) (amplitudeSignalWire p) input then
        if input (negativeWire p) &&
            cnotBasisAction (activeWire p) (amplitudeSignalWire p) input
              (amplitudeSignalWire p) then -1 else 1
      else 0 := by
  rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_operator]
  change
    (onTwoWires (negativeWire p) (amplitudeSignalWire p)
        (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix *
      (cnotBasisEquiv (activeWire p) (amplitudeSignalWire p)
        (activeWire_ne_amplitudeSignalWire p)).permMatrix ℂ) output input = _
  rw [operator_mul_permMatrix_apply]
  change onTwoWires (negativeWire p) (amplitudeSignalWire p)
      (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix output
        (cnotBasisAction (activeWire p) (amplitudeSignalWire p) input) = _
  rw [onTwoWires_apply]
  let moved := cnotBasisAction (activeWire p) (amplitudeSignalWire p) input
  change
    (if SameOutsideTwo (negativeWire p) (amplitudeSignalWire p) output moved then
        localControlledZMatrix
          (output (negativeWire p), output (amplitudeSignalWire p))
          (moved (negativeWire p), moved (amplitudeSignalWire p))
      else 0) =
      if output = moved then
        if input (negativeWire p) && moved (amplitudeSignalWire p) then -1 else 1
      else 0
  have negativePreserved : moved (negativeWire p) = input (negativeWire p) := by
    exact cnotBasisAction_control_or_other _ _ _
      (negativeWire_ne_amplitudeSignalWire p) input
  by_cases outside :
      SameOutsideTwo (negativeWire p) (amplitudeSignalWire p) output moved
  · by_cases localEqual :
        (output (negativeWire p), output (amplitudeSignalWire p)) =
          (moved (negativeWire p), moved (amplitudeSignalWire p))
    · have outputEqual : output = moved := by
        funext wire
        by_cases isNegative : wire = negativeWire p
        · subst wire
          exact congrArg Prod.fst localEqual
        · by_cases isTarget : wire = amplitudeSignalWire p
          · subst wire
            exact congrArg Prod.snd localEqual
          · exact outside wire isNegative isTarget
      subst output
      simp [outside, localControlledZMatrix, moved, negativePreserved]
    · have outputDifferent : output ≠ moved := by
        intro equal
        exact localEqual (by simp [equal])
      simp [outside, localEqual, outputDifferent, localControlledZMatrix]
  · have outputDifferent : output ≠ moved := by
      intro equal
      subst output
      exact outside (by intro wire _ _; rfl)
    simp [outside, outputDifferent]

/-- 埋込みCZは任意状態の各基底振幅へ局所符号を点ごとに掛ける。 -/
theorem applyOperator_embeddedControlledZ
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (state : JointBasis ancillaQubits systemQubits → ℂ)
    (output : JointBasis ancillaQubits systemQubits) :
    applyOperator
        (onTwoWires control target different localControlledZMatrix)
        state output =
      (if output control && output target then -1 else 1) * state output := by
  classical
  unfold applyOperator VerifiedCircuitCore.applyOperator Matrix.mulVec dotProduct
  rw [Fintype.sum_eq_single output]
  · change
      onTwoWires control target different localControlledZMatrix output output *
        state output = _
    rw [onTwoWires_apply]
    have outside : SameOutsideTwo control target output output := by
      intro wire _ _
      rfl
    simp [outside, localControlledZMatrix]
  · intro input inputDifferent
    change
      onTwoWires control target different localControlledZMatrix output input *
        state input = 0
    rw [onTwoWires_apply]
    by_cases outside : SameOutsideTwo control target output input
    · have localDifferent :
          (output control, output target) ≠ (input control, input target) := by
        intro localEqual
        apply inputDifferent
        funext wire
        by_cases isControl : wire = control
        · subst wire
          exact (congrArg Prod.fst localEqual).symm
        · by_cases isTarget : wire = target
          · subst wire
            exact (congrArg Prod.snd localEqual).symm
          · exact (outside wire isControl isTarget).symm
      simp [outside, localControlledZMatrix, localDifferent]
    · simp [outside]

/-- 振幅判定回路の任意状態への作用は、CNOT置換後の振幅へCZ符号を掛ける。 -/
theorem copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_applyOperator
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ)
    (output : JointBasis p.ancillaWidth p.systemWidth) :
    applyOperator
        ((copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator primitiveGateOperator)
        state output =
      (if output (negativeWire p) && output (amplitudeSignalWire p) then -1 else 1) *
        state (cnotBasisAction (activeWire p) (amplitudeSignalWire p) output) := by
  rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_operator]
  rw [show applyOperator
      (onTwoWires (negativeWire p) (amplitudeSignalWire p)
          (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix *
        cnotMatrix (activeWire p) (amplitudeSignalWire p)
          (activeWire_ne_amplitudeSignalWire p)) state =
      applyOperator
        (onTwoWires (negativeWire p) (amplitudeSignalWire p)
          (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix)
        (applyOperator
          (cnotMatrix (activeWire p) (amplitudeSignalWire p)
            (activeWire_ne_amplitudeSignalWire p)) state) by
        unfold applyOperator VerifiedCircuitCore.applyOperator
        exact (Matrix.mulVec_mulVec state _ _).symm]
  rw [applyOperator_embeddedControlledZ]
  change _ *
      applyOperator
        ((cnotBasisEquiv (activeWire p) (amplitudeSignalWire p)
          (activeWire_ne_amplitudeSignalWire p)).permMatrix ℂ) state output = _
  rw [applyOperator_permMatrix]
  rfl

end

end ProbabilityGeneratorQProof
