import QLean.MathematicalSpecifications.KernelReflection
import VerifiedMath.Basis
import QLean.MathematicalSpecifications.CoalescingWalkModel
import VerifiedMath.Complexification
import VerifiedMath.FiniteComplex

/-! Independent mathematical input data for CP01–CP04. -/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications

open scoped BigOperators

noncomputable section

/-- Euclidean norm of a finite complex mathematical state. -/
def stateNorm {basis : Type*} [Fintype basis] (state : basis → ℂ) : ℝ :=
  VerifiedMath.FiniteComplex.norm state

end

end QLean.MathematicalSpecifications

namespace QLean.MathematicalSpecifications.PublicCheckpoints

open Matrix
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.CoalescingWalkModel
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-- Exactly the mathematical data needed to define the Jennings history
matrix.  This record deliberately contains no kernel-reflection scale,
approximation tolerance, or amplitude-amplification parameter. -/
structure HistoryMatrixParameters where
  model : CoalescingWalkModel.Parameters
  clockCount : Nat
  taylorOrder : Nat
  physicalSteps : Nat
  orderCount : Nat
  step : ℝ

/-- Exactly the mathematical data needed to define the kernel reflection and
its successful history branch.  In particular it contains no FPAA or Fourier
error budget. -/
structure KernelReflectionParameters extends HistoryMatrixParameters where
  input : CoalescingWalkModel.Input model
  alphaH : ℝ
  nu : ℝ

/-- State coordinate used by the history-only public input. -/
abbrev HistoryConfiguration (parameters : HistoryMatrixParameters) :=
  CoalescingWalkModel.Configuration parameters.model

/-- Jennings index determined without any downstream checkpoint data. -/
abbrev HistoryMatrixIndex (parameters : HistoryMatrixParameters) :=
  HistoryLinearSystem.Index (HistoryConfiguration parameters)
    parameters.clockCount parameters.orderCount

abbrev KernelConfiguration (parameters : KernelReflectionParameters) :=
  CoalescingWalkModel.Configuration parameters.model

abbrev KernelHistoryIndex (parameters : KernelReflectionParameters) :=
  HistoryLinearSystem.Index (KernelConfiguration parameters)
    parameters.clockCount parameters.orderCount

abbrev KernelExtendedIndex (parameters : KernelReflectionParameters) :=
  Sum (KernelHistoryIndex parameters) Unit

/-- Construct exactly the data that determine the Jennings matrix.  The three
proof arguments are index-domain checks, not implementation or correctness
assumptions.  No initial state or scientific right-hand side occurs here. -/
def historyMatrixDataWithProofs (parameters : HistoryMatrixParameters)
    (order_lt : parameters.taylorOrder < parameters.orderCount)
    (physical_pos : 0 < parameters.physicalSteps)
    (physical_lt : parameters.physicalSteps < parameters.clockCount) :
    HistoryLinearSystem.MatrixData (HistoryConfiguration parameters)
      parameters.clockCount parameters.taylorOrder parameters.physicalSteps
      parameters.orderCount where
  step := parameters.step
  generator := CoalescingWalkModel.generator
  order_lt := order_lt
  physical_pos := physical_pos
  physical_lt := physical_lt

/-- Add the independently supplied scientific initial state to the matrix
data.  This is the first point at which the Jennings right-hand side enters. -/
def historyDataWithProofs (parameters : HistoryMatrixParameters)
    (input : CoalescingWalkModel.Input parameters.model)
    (order_lt : parameters.taylorOrder < parameters.orderCount)
    (physical_pos : 0 < parameters.physicalSteps)
    (physical_lt : parameters.physicalSteps < parameters.clockCount) :
    HistoryLinearSystem.Data (HistoryConfiguration parameters)
      parameters.clockCount parameters.taylorOrder parameters.physicalSteps
      parameters.orderCount where
  toMatrixData := historyMatrixDataWithProofs parameters order_lt physical_pos
    physical_lt
  initial := input.initial

/-- Exactly the index-range conditions needed to define the Jennings history
matrix.  In particular this record contains no hypothesis about the later
kernel reflection, approximation errors, or amplitude amplification. -/
structure HistoryMatrixConditions (parameters : HistoryMatrixParameters) : Prop where
  order_lt : parameters.taylorOrder < parameters.orderCount
  physical_pos : 0 < parameters.physicalSteps
  physical_lt : parameters.physicalSteps < parameters.clockCount

/-- Mathematical conditions required by the kernel reflection itself.  Later
amplification and output error budgets are deliberately absent. -/
structure KernelReflectionConditions
    (parameters : KernelReflectionParameters) : Prop
    extends HistoryMatrixConditions parameters.toHistoryMatrixParameters where
  /-- The right-hand side normalization in `bPlus` is meaningful. -/
  initial_nonzero : parameters.input.initial ≠ 0
  alphaH_pos : 0 < parameters.alphaH
  nu_pos : 0 < parameters.nu
  kernel_invertible : IsUnit
    (KernelReflection.extendedOperator
      (historyDataWithProofs parameters.toHistoryMatrixParameters
        parameters.input order_lt physical_pos physical_lt)
      parameters.alphaH parameters.nu).det

/-- Independent kernel reflection with its minimal public input. -/
def kernelReflectionFor (parameters : KernelReflectionParameters)
    (valid : KernelReflectionConditions parameters) :
    Matrix (KernelExtendedIndex parameters) (KernelExtendedIndex parameters) ℝ :=
  KernelReflection.idealReflection
    (historyDataWithProofs parameters.toHistoryMatrixParameters parameters.input
      valid.order_lt valid.physical_pos valid.physical_lt)
    parameters.alphaH parameters.nu valid.kernel_invertible

/-- The real scalar-extension basis state used by the kernel reflection. -/
def kernelExtensionStateReal (parameters : KernelReflectionParameters) :
    KernelExtendedIndex parameters → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Complex scalar-extension basis: zero on history and one on the extension. -/
def kernelExtensionState (parameters : KernelReflectionParameters) :
    KernelExtendedIndex parameters → ℂ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Project onto the history summand of the minimal kernel-reflection
coordinate space. -/
def kernelHistoryProjector (parameters : KernelReflectionParameters) :
    Matrix (KernelExtendedIndex parameters) (KernelExtendedIndex parameters) ℂ :=
  fun output input =>
    match output, input with
    | Sum.inl outputHistory, Sum.inl inputHistory =>
        if outputHistory = inputHistory then 1 else 0
    | _, _ => 0

/-- Cast a real matrix to the complex scalar field entrywise. -/
def complexifyMatrix {row column : Type*}
    (matrix : Matrix row column ℝ) : Matrix row column ℂ :=
  VerifiedMath.Complexification.matrix matrix

/-- Cast a real state to the complex scalar field entrywise. -/
def complexifyState {index : Type*} (state : index → ℝ) : index → ℂ :=
  VerifiedMath.Complexification.state state

/-- Cast a real Euclidean vector to the complex state used by a circuit. -/
def complexifyVector {index : Type*} [Fintype index]
    (state : EuclideanSpace ℝ index) : index → ℂ :=
  VerifiedMath.Complexification.euclideanVector state

end

end QLean.MathematicalSpecifications.PublicCheckpoints
