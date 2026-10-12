import QLean.SignalProcessing.M13bSpecification
import QLean.History.Integration.ConcreteHistoryInput.Concrete

/-!
# Public M13c specification

M13c extracts the history branch of the M13b clean compression.  Its ideal
target is fixed by the circuit-independent concrete history solution; this is
an unnormalised branch-level L2 statement, with no postselection claim.
-/

open scoped BigOperators
open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open NativeConcreteP18QSPWitness
open NativeSignalQSVTFunctionalBridge
open NativeQSPWitnessTransferModel
open M13bGramBasisStrictPair
open M13bGramFullCompressedAction
open M13bPrimitiveCandidate
open M13bQSVTLogicalEmbedding

namespace M13cSpecification

noncomputable section

/-- Complex-state history projection: retain the history summand and erase
the extension flag. -/
def complexHistoryProjector119 {d c R : Nat}
    (z : State (GramOperator.ExtendedIndex d c R)) :
    State (GramOperator.ExtendedIndex d c R)
  | Sum.inl row => z (Sum.inl row)
  | Sum.inr _ => 0

theorem complexHistoryProjector119_sub {d c R : Nat}
    (x y : State (GramOperator.ExtendedIndex d c R)) :
    complexHistoryProjector119 (x - y) =
      complexHistoryProjector119 x - complexHistoryProjector119 y := by
  funext i
  cases i <;> simp [complexHistoryProjector119]

/-- The complex history projection is L2-contractive. -/
theorem complexHistoryProjector119_contract {d c R : Nat}
    (z : State (GramOperator.ExtendedIndex d c R)) :
    stateL2Norm (complexHistoryProjector119 z) ≤ stateL2Norm z := by
  unfold stateL2Norm
  apply Real.sqrt_le_sqrt
  simp only [Fintype.sum_sum_type]
  have hnonneg :
      0 ≤ ∑ i : Unit, Complex.normSq (z (Sum.inr i)) :=
    Finset.sum_nonneg fun i hi => Complex.normSq_nonneg _
  simpa [complexHistoryProjector119] using
    (le_add_of_nonneg_right hnonneg :
      (∑ i : JenningsHistory.HistoryIndex d c R, Complex.normSq (z (Sum.inl i))) ≤
        (∑ i : JenningsHistory.HistoryIndex d c R, Complex.normSq (z (Sum.inl i))) +
          ∑ i : Unit, Complex.normSq (z (Sum.inr i)))

/-- Complex projection commutes with complexification of the real M13
history projector. -/
theorem complexHistoryProjector119_complexify {d c R : Nat}
    (z : ConcreteHistoryInput.ExtE d c R) :
    complexHistoryProjector119 (complexifyVector z) =
      complexifyVector
        (ConcreteHistoryInput.m13HistoryProjectorEMap (d := d) (c := c) (R := R) z) := by
  funext i
  cases i with
  | inl row =>
      simp [complexHistoryProjector119, complexifyVector,
        VerifiedMath.Complexification.euclideanVector,
        ConcreteHistoryInput.m13HistoryProjectorEMap, ConcreteHistoryInput.matrixEMap,
        ConcreteHistoryInput.toE, ConcreteHistoryInput.m13HistoryProjector, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]
  | inr u =>
      simp [complexHistoryProjector119, complexifyVector,
        VerifiedMath.Complexification.euclideanVector,
        ConcreteHistoryInput.m13HistoryProjectorEMap, ConcreteHistoryInput.matrixEMap,
        ConcreteHistoryInput.toE, ConcreteHistoryInput.m13HistoryProjector, Matrix.mulVec, dotProduct]

/-- Circuit-independent concrete ideal history target. -/
def idealHistoryTarget119 (input : ExecutableInput119) :
    State (executableSignalCleanIndex119 input.source) :=
  complexifyVector (TypedNegativeCases.actualTarget (certifiedInput119 input).base)

end

end M13cSpecification
