import QLean.MathematicalSpecifications.Targets

/-! Proofs relating the direct CP03 mathematical target to its component definitions. -/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.Targets

open Matrix
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.CoalescingWalkModel
open QLean.MathematicalSpecifications.PublicCheckpoints

noncomputable section

/-- The directly displayed three terms are exactly the generic history operator. -/
theorem historyMatrix_eq_operator (parameters : HistoryMatrixParameters)
    (conditions : HistoryMatrixConditions parameters) :
    historyMatrix parameters conditions =
      VerifiedMath.Complexification.matrix (HistoryLinearSystem.operator
        (historyMatrixDataWithProofs parameters conditions.order_lt
          conditions.physical_pos conditions.physical_lt)) := rfl

/-- The CP02-based block matrix inside CP03 is the established Dalzell
extended operator on the same equation data. -/
theorem kernelReflectionMatrix_eq_kernelReflectionFor
    (parameters : KernelReflectionParameters)
    (valid : KernelReflectionConditions parameters) :
    kernelReflectionMatrix parameters valid = kernelReflectionFor parameters valid := by
  dsimp only [kernelReflectionMatrix]
  unfold kernelReflectionFor KernelReflection.idealReflection
    KernelReflection.normalizedKernel KernelReflection.kernelVector
  have hA :
      (fun row column =>
        match row, column with
        | Sum.inl historyRow, Sum.inl historyColumn =>
            (historyMatrix parameters.toHistoryMatrixParameters
              valid.toHistoryMatrixConditions historyRow historyColumn).re /
              parameters.alphaH
        | Sum.inr _, Sum.inr _ => parameters.nu⁻¹
        | _, _ => 0) =
        KernelReflection.extendedOperator
          (historyDataWithProofs parameters.toHistoryMatrixParameters
            parameters.input valid.order_lt valid.physical_pos valid.physical_lt)
          parameters.alphaH parameters.nu := by
    funext row column
    cases row <;> cases column <;>
      rfl
  convert congrArg
    (fun A : Matrix (KernelExtendedIndex parameters)
        (KernelExtendedIndex parameters) ℝ =>
      2 • VerifiedMath.FiniteReal.lineProjector
          (VerifiedMath.FiniteReal.normalize
            (A⁻¹.mulVec
              (KernelReflection.bPlus
                (historyDataWithProofs parameters.toHistoryMatrixParameters
                  parameters.input valid.order_lt valid.physical_pos
                  valid.physical_lt)))) - 1)
    hA using 1
  congr 10
  funext coordinate
  cases coordinate <;> rfl

/-- The direct complex extension state is the same embedded real basis state. -/
theorem kernelExtensionState_eq_real (parameters : KernelReflectionParameters) :
    kernelExtensionState parameters =
      fun coordinate => (kernelExtensionStateReal parameters coordinate : ℂ) := by
  funext coordinate
  cases coordinate <;> rfl

end

end QLean.MathematicalSpecifications.Targets
