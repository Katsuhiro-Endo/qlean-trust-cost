import QLean.MathematicalSpecifications.DelimiterEncoding
import QLean.MathematicalSpecifications.PublicCheckpointData
import VerifiedMath.FiniteReal
import VerifiedMath.FiniteComplex

/-! Four independent mathematical targets for CP01–CP04. -/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.Targets

open Matrix
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.CoalescingWalkModel
open QLean.MathematicalSpecifications.PublicCheckpoints

noncomputable section

/-- CP01 target: the independent generator embedded into the complete
delimiter-sign space.  Every row or column containing an illegal word is
zero by definition. -/
def generatorMatrix (parameters : CoalescingWalkModel.Parameters) :
    Matrix (DelimiterWord parameters) (DelimiterWord parameters) ℂ :=
  fun output input =>
    match decodeConfiguration parameters output,
      decodeConfiguration parameters input with
    | some outputConfiguration, some inputConfiguration =>
        (CoalescingWalkModel.generator
          outputConfiguration inputConfiguration : ℂ)
    | _, _ => 0

/-- CP02 target: the independent complexified Jennings history matrix.
Only the three index-range conditions needed to form that matrix are inputs;
no later kernel-reflection or approximation hypothesis is required. -/
def historyMatrix (parameters : HistoryMatrixParameters)
    (conditions : HistoryMatrixConditions parameters) :
    Matrix (HistoryMatrixIndex parameters) (HistoryMatrixIndex parameters) ℂ :=
  let data := historyMatrixDataWithProofs parameters conditions.order_lt
    conditions.physical_pos conditions.physical_lt
  fun row column =>
    ((HistoryLinearSystem.diagonalEntry row column +
      HistoryLinearSystem.withinBlockEntry data row column +
      HistoryLinearSystem.betweenBlockEntry data row column : ℝ) : ℂ)

/-- CP03: `R = 2 P_z - I` from public CP02 via `A = diag(H/alpha_H,nu⁻¹)`. -/
def kernelReflectionMatrix (parameters : KernelReflectionParameters)
    (valid : KernelReflectionConditions parameters) :
    Matrix (KernelExtendedIndex parameters) (KernelExtendedIndex parameters) ℝ :=
  let H : Matrix (HistoryMatrixIndex parameters.toHistoryMatrixParameters)
      (HistoryMatrixIndex parameters.toHistoryMatrixParameters) ℝ :=
    fun row column =>
      (historyMatrix parameters.toHistoryMatrixParameters
        valid.toHistoryMatrixConditions row column).re
  let A : Matrix (KernelExtendedIndex parameters)
      (KernelExtendedIndex parameters) ℝ := fun row column =>
    match row, column with
    | Sum.inl historyRow, Sum.inl historyColumn =>
        H historyRow historyColumn / parameters.alphaH
    | Sum.inr _, Sum.inr _ => parameters.nu⁻¹
    | _, _ => 0
  let b : KernelHistoryIndex parameters → ℝ := fun row =>
    if row.clock.val = 0 ∧ row.order.val = 0 then
      parameters.input.initial row.state else 0
  let bPlus : KernelExtendedIndex parameters → ℝ := fun coordinate =>
    match coordinate with
    | Sum.inl history => VerifiedMath.FiniteReal.normalize b history / Real.sqrt 2
    | Sum.inr _ => 1 / Real.sqrt 2
  let z := A⁻¹.mulVec bPlus
  2 • VerifiedMath.FiniteReal.lineProjector
      (VerifiedMath.FiniteReal.normalize z) - 1

/-- CP04 target: the non-normalised successful history vector. -/
def successfulHistoryState (parameters : KernelReflectionParameters)
    (valid : KernelReflectionConditions parameters) :
    KernelExtendedIndex parameters → ℂ :=
  (kernelHistoryProjector parameters).mulVec
    ((VerifiedMath.Complexification.matrix (kernelReflectionMatrix parameters valid)).mulVec
      (kernelExtensionState parameters))



end

end QLean.MathematicalSpecifications.Targets
