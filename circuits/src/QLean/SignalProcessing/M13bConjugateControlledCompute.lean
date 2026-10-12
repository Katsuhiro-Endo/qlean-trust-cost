import QLean.SignalProcessing.M13bConjugatePhaseWord
import QLean.SignalProcessing.M13bControlledStateSemantics

/-!
# M13b: externally controlled phase-conjugate compute words

This module compiles two independently selected, same-direction QSP words.
Both use the existing leaf-wise external-control compiler; no supplied
operator equality or synthetic projector is introduced.
-/

set_option autoImplicit false

namespace M13bConjugateControlledCompute

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open SpectralSamplingProof.Analytic

noncomputable section

/-- Positive-control action of the mathematical lift on one clean basis ket. -/
theorem controlledLift_apply_control_one_basis
    (n : Nat) (operator : Operator (QubitBasis n)) (input : QubitBasis n) :
    applyOperator
      (externallyControlledWireLiftOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
      (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n true input)) =
      M13bControlledStateSemantics.m13bControlledState n true
        (applyOperator operator (basisKet input)) := by
  funext output
  rw [applyOperator_basisKet, externallyControlledWireLiftOperator_apply,
    if_pos (M13bExternallyControlledCompute.m13bControlledBasis_control n true input)]
  simpa [M13bControlledStateSemantics.m13bControlledState,
    M13bExternallyControlledCompute.m13bControlledBasis] using
    congrFun (applyOperator_wireLiftOperator_fixedOutsideBasisKet
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).placement
      (M13bExternallyControlledCompute.m13bControlOutside n true) operator input) output

/-- False external control is exactly the identity on one clean basis ket. -/
theorem controlledLift_apply_control_zero_basis
    (n : Nat) (operator : Operator (QubitBasis n)) (input : QubitBasis n) :
    applyOperator
      (externallyControlledWireLiftOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
      (basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input)) =
      basisKet (M13bExternallyControlledCompute.m13bControlledBasis n false input) := by
  funext output
  rw [applyOperator_basisKet, externallyControlledWireLiftOperator_apply]
  have hcontrol : M13bExternallyControlledCompute.m13bControlledBasis n false input
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).control ≠ true := by
    rw [M13bExternallyControlledCompute.m13bControlledBasis_control]
    decide
  rw [if_neg hcontrol]
  rfl

/-- Positive external control acts on every coherent clean state by the
underlying source operator. -/
theorem controlledLift_apply_control_one_state
    (n : Nat) (operator : Operator (QubitBasis n))
    (state : State (QubitBasis n)) :
    applyOperator
      (externallyControlledWireLiftOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
      (M13bControlledStateSemantics.m13bControlledState n true state) =
      M13bControlledStateSemantics.m13bControlledState n true
        (applyOperator operator state) := by
  classical
  calc
    applyOperator
        (externallyControlledWireLiftOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
        (M13bControlledStateSemantics.m13bControlledState n true state) =
      applyOperator
        (externallyControlledWireLiftOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
        (M13bControlledStateSemantics.m13bControlledState n true
          (∑ input : QubitBasis n, state input • basisKet input)) := by
            congr 2
            exact state_eq_sum_smul_basisKet119 state
    _ = ∑ input : QubitBasis n, state input •
          applyOperator
            (externallyControlledWireLiftOperator
              (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
            (M13bControlledStateSemantics.m13bControlledState n true
              (basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [fixedOutsideStateEmbedding_smul119]
            rw [applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
    _ = ∑ input : QubitBasis n, state input •
          M13bControlledStateSemantics.m13bControlledState n true
            (applyOperator operator (basisKet input)) := by
            apply Finset.sum_congr rfl
            intro input _
            apply congrArg (fun result => state input • result)
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_basisKet]
            exact controlledLift_apply_control_one_basis n operator input
    _ = M13bControlledStateSemantics.m13bControlledState n true
          (applyOperator operator
            (∑ input : QubitBasis n, state input • basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
            rw [fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [fixedOutsideStateEmbedding_smul119]
    _ = M13bControlledStateSemantics.m13bControlledState n true
          (applyOperator operator state) := by
            rw [← state_eq_sum_smul_basisKet119 state]

/-- False external control is the identity on every coherent clean state. -/
theorem controlledLift_apply_control_zero_state
    (n : Nat) (operator : Operator (QubitBasis n))
    (state : State (QubitBasis n)) :
    applyOperator
      (externallyControlledWireLiftOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
      (M13bControlledStateSemantics.m13bControlledState n false state) =
      M13bControlledStateSemantics.m13bControlledState n false state := by
  classical
  calc
    applyOperator
        (externallyControlledWireLiftOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
        (M13bControlledStateSemantics.m13bControlledState n false state) =
      applyOperator
        (externallyControlledWireLiftOperator
          (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
        (M13bControlledStateSemantics.m13bControlledState n false
          (∑ input : QubitBasis n, state input • basisKet input)) := by
            congr 2
            exact state_eq_sum_smul_basisKet119 state
    _ = ∑ input : QubitBasis n, state input •
          applyOperator
            (externallyControlledWireLiftOperator
              (M13bExternallyControlledCompute.m13bExternalControlLayout n) operator)
            (M13bControlledStateSemantics.m13bControlledState n false
              (basisKet input)) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [fixedOutsideStateEmbedding_smul119]
            rw [applyOperator_finset_sum119]
            simp_rw [applyOperator_smul]
    _ = ∑ input : QubitBasis n, state input •
          M13bControlledStateSemantics.m13bControlledState n false
            (basisKet input) := by
            apply Finset.sum_congr rfl
            intro input _
            apply congrArg (fun result => state input • result)
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_basisKet]
            exact controlledLift_apply_control_zero_basis n operator input
    _ = M13bControlledStateSemantics.m13bControlledState n false
          (∑ input : QubitBasis n, state input • basisKet input) := by
            unfold M13bControlledStateSemantics.m13bControlledState
            rw [fixedOutsideStateEmbedding_finset_sum119]
            simp_rw [fixedOutsideStateEmbedding_smul119]
    _ = M13bControlledStateSemantics.m13bControlledState n false state := by
            rw [← state_eq_sum_smul_basisKet119 state]

end

end M13bConjugateControlledCompute
