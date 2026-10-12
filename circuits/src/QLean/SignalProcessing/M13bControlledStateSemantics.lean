import QLean.SignalProcessing.M13bExternallyControlledCompute

/-!
# M13b: controlled compute on arbitrary clean states

The leaf-wise external-control compiler states correctness on its clean work
subspace.  This module upgrades the already-proved basis-ket branches to the
whole fixed-outside state block.  In particular, the controlled circuit is not
only an entrywise candidate: it acts as `U` (or `U†`) on every coherent source
state whose two compiler work wires are clean.
-/

set_option autoImplicit false

namespace M13bControlledStateSemantics

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness

noncomputable section

/-- Embed an arbitrary source state with an explicit external control and
both compiler work wires clean. -/
def m13bControlledState (n : Nat) (controlValue : Bool)
    (state : State (QubitBasis n)) : State (QubitBasis (n + 3)) :=
  fixedOutsideStateEmbedding (M13bExternallyControlledCompute.m13bExternalControlLayout n).placement
    (M13bExternallyControlledCompute.m13bControlOutside n controlValue) state

/-- Every state in the fixed-outside control block lies in the compiler's
coherent clean-work span, not merely its individual computational basis kets. -/
theorem m13bControlledState_mem_clean
    (n : Nat) (controlValue : Bool) (state : State (QubitBasis n)) :
    m13bControlledState n controlValue state ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate
          (M13bExternallyControlledCompute.m13bExternalControlCleanWorkValid n)) := by
  classical
  unfold m13bControlledState
  rw [state_eq_sum_smul_basisKet119 state]
  rw [fixedOutsideStateEmbedding_finset_sum119]
  simp_rw [fixedOutsideStateEmbedding_smul119]
  apply Submodule.sum_mem
  intro input _
  apply (SubspaceMapComponent.basisSpan
    (externallyControlledCleanWorkPredicate
      (M13bExternallyControlledCompute.m13bExternalControlCleanWorkValid n))).smul_mem
  rw [fixedOutsideStateEmbedding_basisKet]
  exact SubspaceMapComponent.basisKet_mem_basisSpan
    (M13bExternallyControlledCompute.m13bControlledBasis_work_clean
      n controlValue input)

end

end M13bControlledStateSemantics
