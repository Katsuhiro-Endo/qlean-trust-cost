import QLean.SignalProcessing.M13bControlledStateSemantics
import QLean.Circuits.Foundation.ShuklaVedulaUniformCorrectness

set_option autoImplicit false

namespace M13bHadamardBasisSemanticVerification

open VerifiedCircuitCore

theorem replace_false_eq_of_true
    {qubits : Nat} (input output : QubitBasis qubits) (target : Fin qubits)
    (outputTrue : output target = true)
    (replaced : replaceQubitWire output target false = input) :
    output = replaceQubitWire input target true := by
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [outputTrue]
  · have atWire := congrFun replaced wire
    rw [replaceQubitWire_outside output target wire false equal] at atWire
    rw [replaceQubitWire_outside input target wire true equal]
    exact atWire

theorem replace_true_ne_of_input_false
    {qubits : Nat} (input output : QubitBasis qubits) (target : Fin qubits)
    (inputFalse : input target = false) :
    replaceQubitWire output target true ≠ input := by
  intro equal
  have atTarget := congrArg (fun basis : QubitBasis qubits => basis target) equal
  simp [inputFalse] at atTarget

theorem m13b_replace_control_false_true (n : Nat) (input : QubitBasis n) :
    replaceQubitWire
      (M13bExternallyControlledCompute.m13bControlledBasis n false input)
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).control true =
    M13bExternallyControlledCompute.m13bControlledBasis n true input := by
  funext wire
  by_cases same : wire = (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
  · subst wire
    rw [replaceQubitWire]
    simp [M13bExternallyControlledCompute.m13bControlledBasis_control]
  · rw [replaceQubitWire_outside _ _ _ true same]
    simp [M13bExternallyControlledCompute.m13bControlledBasis,
      M13bExternallyControlledCompute.m13bControlOutside,
      fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, same]

theorem m13bHadamard_basis_false (n : Nat) (input : QubitBasis n) :
    applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
      (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input)) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input) +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input) := by
  let control := (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
  let inputBasis := M13bExternallyControlledCompute.m13bControlledBasis n false input
  let trueBasis := M13bExternallyControlledCompute.m13bControlledBasis n true input
  have inputFalse : inputBasis control = false := by
    dsimp [inputBasis, control]
    exact M13bExternallyControlledCompute.m13bControlledBasis_control n false input
  have trueBasisEq : replaceQubitWire inputBasis control true = trueBasis := by
    dsimp [inputBasis, control, trueBasis]
    funext wire
    by_cases same : wire = (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
    · subst wire
      rw [replaceQubitWire]
      simp [M13bExternallyControlledCompute.m13bControlledBasis_control]
    · rw [replaceQubitWire_outside _ _ _ true same]
      simp [M13bExternallyControlledCompute.m13bControlledBasis,
        M13bExternallyControlledCompute.m13bControlOutside,
        fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, same]
  funext output
  rw [applyOperator_embedSingleQubitOperator_state, Fintype.sum_bool]
  by_cases outputTrue : output control = true
  · have replaceTrueNe := replace_true_ne_of_input_false
      inputBasis output control inputFalse
    have outputEq :
        replaceQubitWire output control false = inputBasis ↔ output = trueBasis := by
      constructor
      · intro equal
        rw [replace_false_eq_of_true inputBasis output control outputTrue equal]
        exact trueBasisEq
      · intro equal
        subst output
        rw [← trueBasisEq]
        funext wire
        by_cases wireEq : wire = control
        · subst wire
          simp [inputFalse]
        · simp [replaceQubitWire_outside, wireEq]
    have outputNe : output ≠ inputBasis := by
      intro equal
      have atTarget := congrArg (fun basis : QubitBasis (n + 3) => basis control) equal
      simp [outputTrue, inputFalse] at atTarget
    dsimp [control, inputBasis, trueBasis] at *
    simp [localH, basisKet, outputTrue, replaceTrueNe, outputEq,
      outputNe]
  · have outputFalse : output control = false :=
      Bool.eq_false_of_not_eq_true outputTrue
    have replaceFalse : replaceQubitWire output control false = output := by
      simpa [outputFalse] using replaceQubitWire_self output control
    have replaceTrueNe := replace_true_ne_of_input_false
      inputBasis output control inputFalse
    have flippedNe : output ≠ trueBasis := by
      intro equal
      have atTarget := congrArg (fun basis : QubitBasis (n + 3) => basis control) equal
      have trueControl : trueBasis control = true := by
        dsimp [trueBasis, control]
        exact M13bExternallyControlledCompute.m13bControlledBasis_control n true input
      simp [outputFalse, trueControl] at atTarget
    dsimp [control, inputBasis, trueBasis] at *
    simp [localH, basisKet, outputFalse, replaceFalse, replaceTrueNe,
      flippedNe]

theorem m13bHadamard_state_false (n : Nat) (state : State (QubitBasis n)) :
    applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
      (M13bControlledStateSemantics.m13bControlledState n false state) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state := by
  classical
  let hscale : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  calc
    applyOperator
        (embedSingleQubitOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
        (M13bControlledStateSemantics.m13bControlledState n false state) =
      applyOperator
        (embedSingleQubitOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
        (M13bControlledStateSemantics.m13bControlledState n false
          (∑ input : QubitBasis n, state input • basisKet input)) := by
            congr 2
            exact NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state
    _ = ∑ input : QubitBasis n, state input •
        applyOperator
          (embedSingleQubitOperator
            (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
          (M13bControlledStateSemantics.m13bControlledState n false (basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
            rw [NativeConcreteP18QSPWitness.applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
    _ = ∑ input : QubitBasis n, state input •
        (hscale • basisKet
          (M13bExternallyControlledCompute.m13bControlledBasis n false input) +
        hscale • basisKet
          (M13bExternallyControlledCompute.m13bControlledBasis n true input)) := by
            apply Finset.sum_congr rfl
            intro input _
            apply congrArg (fun result => state input • result)
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_basisKet]
            change applyOperator
              (embedSingleQubitOperator
                (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
              (basisKet
                (M13bExternallyControlledCompute.m13bControlledBasis n false input)) = _
            simpa [hscale] using m13bHadamard_basis_false n input
    _ = hscale • M13bControlledStateSemantics.m13bControlledState n false state +
        hscale • M13bControlledStateSemantics.m13bControlledState n true state := by
            simp_rw [smul_add, smul_smul]
            rw [Finset.sum_add_distrib]
            have hfalse : hscale •
                M13bControlledStateSemantics.m13bControlledState n false state =
                ∑ input : QubitBasis n, hscale •
                  (state input • basisKet
                    (M13bExternallyControlledCompute.m13bControlledBasis n false input)) := by
              calc
                hscale • M13bControlledStateSemantics.m13bControlledState n false state =
                    hscale • M13bControlledStateSemantics.m13bControlledState n false
                      (∑ input : QubitBasis n, state input • basisKet input) := by
                        congr 2
                        exact NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state
                _ = hscale • ∑ input : QubitBasis n, state input • basisKet
                    (M13bExternallyControlledCompute.m13bControlledBasis n false input) := by
                      unfold M13bControlledStateSemantics.m13bControlledState
                      rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
                      simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
                      simp_rw [fixedOutsideStateEmbedding_basisKet]
                      change hscale • ∑ input : QubitBasis n, state input • basisKet
                        (M13bExternallyControlledCompute.m13bControlledBasis n false input) = _
                      rfl
                _ = _ := by rw [Finset.smul_sum]
            have htrue : hscale •
                M13bControlledStateSemantics.m13bControlledState n true state =
                ∑ input : QubitBasis n, hscale •
                  (state input • basisKet
                    (M13bExternallyControlledCompute.m13bControlledBasis n true input)) := by
              calc
                hscale • M13bControlledStateSemantics.m13bControlledState n true state =
                    hscale • M13bControlledStateSemantics.m13bControlledState n true
                      (∑ input : QubitBasis n, state input • basisKet input) := by
                        congr 2
                        exact NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state
                _ = hscale • ∑ input : QubitBasis n, state input • basisKet
                    (M13bExternallyControlledCompute.m13bControlledBasis n true input) := by
                      unfold M13bControlledStateSemantics.m13bControlledState
                      rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
                      simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
                      simp_rw [fixedOutsideStateEmbedding_basisKet]
                      change hscale • ∑ input : QubitBasis n, state input • basisKet
                        (M13bExternallyControlledCompute.m13bControlledBasis n true input) = _
                      rfl
                _ = _ := by rw [Finset.smul_sum]
            rw [hfalse, htrue]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro input _
              simp only [smul_smul]
              rw [mul_comm]
            · apply Finset.sum_congr rfl
              intro input _
              simp only [smul_smul]
              rw [mul_comm]
    _ = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state := by
          rfl

end M13bHadamardBasisSemanticVerification
