import QLean.SignalProcessing.M13bHadamardStateSemantics

/-!
# M13b: the control-one Hadamard branch

The second physical Hadamard in the Hermitian wrapper must be evaluated on
both coherent control branches.  This file supplies the control-one branch,
with the sign fixed by the primitive `localH` matrix.
-/

set_option autoImplicit false

namespace M13bHadamardTrueStateSemantics

open VerifiedCircuitCore

noncomputable section

theorem replace_false_ne_of_input_true
    {qubits : Nat} (input output : QubitBasis qubits) (target : Fin qubits)
    (inputTrue : input target = true) :
    replaceQubitWire output target false ≠ input := by
  intro equal
  have atTarget := congrArg (fun basis : QubitBasis qubits => basis target) equal
  simp [inputTrue] at atTarget

theorem m13b_replace_control_true_false (n : Nat) (input : QubitBasis n) :
    replaceQubitWire
      (M13bExternallyControlledCompute.m13bControlledBasis n true input)
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).control false =
    M13bExternallyControlledCompute.m13bControlledBasis n false input := by
  funext wire
  by_cases same : wire =
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
  · subst wire
    rw [replaceQubitWire]
    simp [M13bExternallyControlledCompute.m13bControlledBasis_control]
  · rw [replaceQubitWire_outside _ _ _ false same]
    simp [M13bExternallyControlledCompute.m13bControlledBasis,
      M13bExternallyControlledCompute.m13bControlOutside,
      fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, same]

theorem m13bHadamard_basis_true (n : Nat) (input : QubitBasis n) :
    applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
      (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input)) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input) -
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input) := by
  let control := (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
  let inputBasis := M13bExternallyControlledCompute.m13bControlledBasis n true input
  let falseBasis := M13bExternallyControlledCompute.m13bControlledBasis n false input
  have inputTrue : inputBasis control = true := by
    dsimp [inputBasis, control]
    exact M13bExternallyControlledCompute.m13bControlledBasis_control n true input
  have falseBasisEq : replaceQubitWire inputBasis control false = falseBasis := by
    dsimp [inputBasis, control, falseBasis]
    exact m13b_replace_control_true_false n input
  funext output
  rw [applyOperator_embedSingleQubitOperator_state, Fintype.sum_bool]
  by_cases outputTrue : output control = true
  · have replaceFalseNe := replace_false_ne_of_input_true
      inputBasis output control inputTrue
    have replaceTrue : replaceQubitWire output control true = output := by
      simpa [outputTrue] using replaceQubitWire_self output control
    have outputNeFalse : output ≠ falseBasis := by
      intro equal
      have atTarget := congrArg (fun basis : QubitBasis (n + 3) => basis control) equal
      have falseControl : falseBasis control = false := by
        dsimp [falseBasis, control]
        exact M13bExternallyControlledCompute.m13bControlledBasis_control n false input
      simp [outputTrue, falseControl] at atTarget
    dsimp [control, inputBasis, falseBasis] at *
    simp [localH, basisKet, outputTrue, replaceFalseNe, replaceTrue,
      outputNeFalse]
    by_cases outputEq : output =
        M13bExternallyControlledCompute.m13bControlledBasis n true input <;>
      simp [outputEq]
  · have outputFalse : output control = false :=
      Bool.eq_false_of_not_eq_true outputTrue
    have replaceFalse : replaceQubitWire output control false = output := by
      simpa [outputFalse] using replaceQubitWire_self output control
    have outputNeInput : output ≠ inputBasis := by
      intro equal
      have atTarget := congrArg (fun basis : QubitBasis (n + 3) => basis control) equal
      simp [outputFalse, inputTrue] at atTarget
    have outputEq : replaceQubitWire output control true = inputBasis ↔
        output = falseBasis := by
      constructor
      · intro equal
        have result : output = replaceQubitWire inputBasis control false := by
          funext wire
          by_cases wireEq : wire = control
          · subst wire
            rw [replaceQubitWire]
            simp [outputFalse]
          · have atWire := congrFun equal wire
            rw [replaceQubitWire_outside output control wire true wireEq] at atWire
            rw [replaceQubitWire_outside inputBasis control wire false wireEq]
            exact atWire
        rw [result, falseBasisEq]
      · intro equal
        subst output
        rw [← falseBasisEq]
        funext wire
        by_cases wireEq : wire = control
        · subst wire
          simp [inputTrue]
        · simp [replaceQubitWire_outside, wireEq]
    dsimp [control, inputBasis, falseBasis] at *
    simp [localH, basisKet, outputFalse, replaceFalse, outputNeInput, outputEq]

theorem m13bHadamard_state_true (n : Nat) (state : State (QubitBasis n)) :
    applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
      (M13bControlledStateSemantics.m13bControlledState n true state) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state -
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state := by
  classical
  let hscale : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  calc
    applyOperator
        (embedSingleQubitOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
        (M13bControlledStateSemantics.m13bControlledState n true state) =
      applyOperator
        (embedSingleQubitOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
        (M13bControlledStateSemantics.m13bControlledState n true
          (∑ input : QubitBasis n, state input • basisKet input)) := by
            congr 2
            exact NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state
    _ = ∑ input : QubitBasis n, state input •
        applyOperator
          (embedSingleQubitOperator
            (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
          (M13bControlledStateSemantics.m13bControlledState n true (basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
            rw [NativeConcreteP18QSPWitness.applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
    _ = ∑ input : QubitBasis n, state input •
        (hscale • basisKet
          (M13bExternallyControlledCompute.m13bControlledBasis n false input) -
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
                (M13bExternallyControlledCompute.m13bControlledBasis n true input)) = _
            simpa [hscale] using m13bHadamard_basis_true n input
    _ = hscale • M13bControlledStateSemantics.m13bControlledState n false state -
        hscale • M13bControlledStateSemantics.m13bControlledState n true state := by
            simp_rw [smul_sub, smul_smul]
            rw [Finset.sum_sub_distrib]
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
                      rfl
                _ = _ := by rw [Finset.smul_sum]
            rw [hfalse, htrue]
            apply congrArg₂ (· - ·)
            · apply Finset.sum_congr rfl
              intro input _
              simp only [smul_smul]
              rw [mul_comm]
            · apply Finset.sum_congr rfl
              intro input _
              simp only [smul_smul]
              rw [mul_comm]
    _ = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state -
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state := by
          rfl

theorem cleanControlH_actual_apply_control_true_state
    (symbolValue : String → ℝ) (n : Nat) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (M13bExternallyControlledCompute.m13bCleanControlHComponent
        symbolValue n).circuit)
      (M13bControlledStateSemantics.m13bControlledState n true state) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state -
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state := by
  exact m13bHadamard_state_true n state

end

end M13bHadamardTrueStateSemantics
