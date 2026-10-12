import QLean.SignalProcessing.M13cSpecification
import QLean.History.Jennings.PureSpec
import QLean.History.Jennings.ProofEstablishedBridge
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import Mathlib
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bHermitianSuccessReflection

namespace M15bPhysicalSpecification

noncomputable section

/-! Norm contraction for the adjoint of a history-basis embedding. -/

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open NativeSingularPairTwoFrame
open SpectralSamplingProof.Analytic

/-- The adjoint of a finite basis-ket embedding is L2-contractive. -/
theorem stateL2Norm_conjTranspose_basisKetEmbedding_le119
    {logical physical : Type*} [Fintype logical] [Fintype physical]
    [DecidableEq logical] [DecidableEq physical]
    (embedding : logical ↪ physical) (z : State physical) :
    stateL2Norm ((Matrix.conjTranspose (basisKetEmbeddingMatrix embedding)).mulVec z) ≤
      stateL2Norm z := by
  unfold stateL2Norm
  apply Real.sqrt_le_sqrt
  have hcoord (i : logical) :
      ((Matrix.conjTranspose (basisKetEmbeddingMatrix embedding)).mulVec z) i = z (embedding i) := by
    simp only [basisKetEmbeddingMatrix, Matrix.conjTranspose_apply,
      Matrix.mulVec, dotProduct, basisKet]
    rw [Finset.sum_eq_single (embedding i)]
    · simp
    · intro other _ different
      simp [different]
    · simp
  simp_rw [hcoord]
  have hsum :
      (∑ i, Complex.normSq (z (embedding i))) =
        ∑ p ∈ Finset.univ.image embedding, Complex.normSq (z p) := by
    rw [Finset.sum_image]
    intro a _ b _ equal
    exact embedding.injective equal
  rw [hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _)
  · intro _ _ _
    exact Complex.normSq_nonneg _

set_option maxHeartbeats 800000 in

-- Reversing a symbol-free comparator list restores any clean-data basis
-- state from its computed flag.
set_option maxHeartbeats 800000 in

-- On an arbitrary clean physical-data basis state, compute--phase--uncompute
-- returns every work wire to zero and applies precisely the comparator-list
-- projector phase.
set_option maxHeartbeats 800000 in

-- The clean-data compression of an arbitrary comparator-list phase is the
-- corresponding projector phase on the full physical data Hilbert space.
set_option maxHeartbeats 800000 in

-- Reversing the lifted preparation compresses to the adjoint of the M13b
-- primitive operator.
set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 2400000 in

/- A legacy schedule-specific component retained for compatibility. -/
set_option maxHeartbeats 2400000 in

set_option maxHeartbeats 2400000 in

end

end M15bPhysicalSpecification
