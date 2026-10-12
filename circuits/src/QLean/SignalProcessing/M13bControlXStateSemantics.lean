import QLean.SignalProcessing.M13bHadamardStateSemantics

/-!
# M13b: physical external-control X semantics

The selector uses two primitive X gates to swap its clean external-control
branches.  This module proves that action on whole coherent fixed-outside
state blocks.
-/

set_option autoImplicit false

namespace M13bControlXStateSemantics

open VerifiedCircuitCore

noncomputable section

theorem m13b_xor_false_to_true
    (n : Nat) (input : QubitBasis n) :
    xorWire (M13bExternallyControlledCompute.m13bExternalControlLayout n).control true
      (M13bExternallyControlledCompute.m13bControlledBasis n false input) =
    M13bExternallyControlledCompute.m13bControlledBasis n true input := by
  let control := (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
  let basis := M13bExternallyControlledCompute.m13bControlledBasis n false input
  have basisFalse : basis control = false := by
    dsimp [basis, control]
    exact M13bExternallyControlledCompute.m13bControlledBasis_control n false input
  calc
    xorWire control true basis = replaceQubitWire basis control true := by
      funext wire
      by_cases same : wire = control
      · subst wire
        simp [xorWire, replaceQubitWire, basisFalse]
      · simp [xorWire, replaceQubitWire, same]
    _ = M13bExternallyControlledCompute.m13bControlledBasis n true input := by
      dsimp [basis, control]
      exact M13bHadamardBasisSemanticVerification.m13b_replace_control_false_true n input

theorem m13b_xor_true_to_false
    (n : Nat) (input : QubitBasis n) :
    xorWire (M13bExternallyControlledCompute.m13bExternalControlLayout n).control true
      (M13bExternallyControlledCompute.m13bControlledBasis n true input) =
    M13bExternallyControlledCompute.m13bControlledBasis n false input := by
  let control := (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
  let basis := M13bExternallyControlledCompute.m13bControlledBasis n true input
  have basisTrue : basis control = true := by
    dsimp [basis, control]
    exact M13bExternallyControlledCompute.m13bControlledBasis_control n true input
  calc
    xorWire control true basis = replaceQubitWire basis control false := by
      funext wire
      by_cases same : wire = control
      · subst wire
        simp [xorWire, replaceQubitWire, basisTrue]
      · simp [xorWire, replaceQubitWire, same]
    _ = M13bExternallyControlledCompute.m13bControlledBasis n false input := by
      funext wire
      by_cases same : wire = control
      · subst wire
        rw [replaceQubitWire]
        dsimp [control, basis]
        rw [if_pos rfl]
        exact (M13bExternallyControlledCompute.m13bControlledBasis_control
          n false input).symm
      · rw [replaceQubitWire_outside _ _ _ false same]
        have different : wire ≠
            (M13bExternallyControlledCompute.m13bExternalControlLayout n).control := by
          simpa [control] using same
        dsimp [basis, control]
        simp [M13bExternallyControlledCompute.m13bControlledBasis,
          M13bExternallyControlledCompute.m13bControlOutside,
          fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, different]

theorem controlX_basis_false
    (symbolValue : String → ℝ) (n : Nat) (input : QubitBasis n) :
    applyOperator (primitiveGateOperatorWithSymbols symbolValue
      (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
      (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input)) =
      basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input) := by
  rw [primitiveXOperator_eq_deterministicOperator,
    applyOperator_deterministicOperator_basisKet]
  congr 1
  exact m13b_xor_false_to_true n input

theorem controlX_basis_true
    (symbolValue : String → ℝ) (n : Nat) (input : QubitBasis n) :
    applyOperator (primitiveGateOperatorWithSymbols symbolValue
      (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
      (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input)) =
      basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input) := by
  rw [primitiveXOperator_eq_deterministicOperator,
    applyOperator_deterministicOperator_basisKet]
  congr 1
  exact m13b_xor_true_to_false n input

theorem controlX_state_false
    (symbolValue : String → ℝ) (n : Nat) (state : State (QubitBasis n)) :
    applyOperator (primitiveGateOperatorWithSymbols symbolValue
      (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
      (M13bControlledStateSemantics.m13bControlledState n false state) =
      M13bControlledStateSemantics.m13bControlledState n true state := by
  classical
  calc
    applyOperator (primitiveGateOperatorWithSymbols symbolValue
        (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
        (M13bControlledStateSemantics.m13bControlledState n false state) =
      applyOperator (primitiveGateOperatorWithSymbols symbolValue
        (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
        (M13bControlledStateSemantics.m13bControlledState n false
          (∑ input : QubitBasis n, state input • basisKet input)) := by
            congr 2
            exact NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state
    _ = ∑ input : QubitBasis n, state input •
        applyOperator (primitiveGateOperatorWithSymbols symbolValue
          (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
          (M13bControlledStateSemantics.m13bControlledState n false (basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
            rw [NativeConcreteP18QSPWitness.applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
    _ = ∑ input : QubitBasis n, state input •
        basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input) := by
            apply Finset.sum_congr rfl
            intro input _
            apply congrArg (fun result => state input • result)
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_basisKet]
            change applyOperator (primitiveGateOperatorWithSymbols symbolValue
              (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
              (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input)) = _
            exact controlX_basis_false symbolValue n input
    _ = M13bControlledStateSemantics.m13bControlledState n true
        (∑ input : QubitBasis n, state input • basisKet input) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
            simp_rw [fixedOutsideStateEmbedding_basisKet]
            rfl
    _ = M13bControlledStateSemantics.m13bControlledState n true state := by
            rw [← NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state]

theorem controlX_state_true
    (symbolValue : String → ℝ) (n : Nat) (state : State (QubitBasis n)) :
    applyOperator (primitiveGateOperatorWithSymbols symbolValue
      (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
      (M13bControlledStateSemantics.m13bControlledState n true state) =
      M13bControlledStateSemantics.m13bControlledState n false state := by
  classical
  calc
    applyOperator (primitiveGateOperatorWithSymbols symbolValue
        (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
        (M13bControlledStateSemantics.m13bControlledState n true state) =
      applyOperator (primitiveGateOperatorWithSymbols symbolValue
        (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
        (M13bControlledStateSemantics.m13bControlledState n true
          (∑ input : QubitBasis n, state input • basisKet input)) := by
            congr 2
            exact NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state
    _ = ∑ input : QubitBasis n, state input •
        applyOperator (primitiveGateOperatorWithSymbols symbolValue
          (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
          (M13bControlledStateSemantics.m13bControlledState n true (basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
            rw [NativeConcreteP18QSPWitness.applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
    _ = ∑ input : QubitBasis n, state input •
        basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input) := by
            apply Finset.sum_congr rfl
            intro input _
            apply congrArg (fun result => state input • result)
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_basisKet]
            change applyOperator (primitiveGateOperatorWithSymbols symbolValue
              (.x (M13bExternallyControlledCompute.m13bExternalControlLayout n).control))
              (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input)) = _
            exact controlX_basis_true symbolValue n input
    _ = M13bControlledStateSemantics.m13bControlledState n false
        (∑ input : QubitBasis n, state input • basisKet input) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [NativeConcreteP18QSPWitness.fixedOutsideStateEmbedding_smul119]
            simp_rw [fixedOutsideStateEmbedding_basisKet]
            rfl
    _ = M13bControlledStateSemantics.m13bControlledState n false state := by
            rw [← NativeConcreteP18QSPWitness.state_eq_sum_smul_basisKet119 state]

end

end M13bControlXStateSemantics
