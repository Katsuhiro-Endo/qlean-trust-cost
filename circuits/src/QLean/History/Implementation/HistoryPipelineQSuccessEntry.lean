import QLean.History.Implementation.HistoryPipelineRepairedH3
import QLean.History.Foundation.M09Bridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open scoped Matrix.Norms.L2Operator
open VerifiedCircuitCore
open ProbabilityGeneratorQProof

noncomputable section

theorem recordedFullSpaceQ_success_entry119
    (p : QParameters)
    (output input : RegisterBasis p.systemWidth) :
    HistoryBlockEncoding.M09Bridge.recordedFullSpaceQ p
        (combineBasis (allZeroAncilla p.ancillaWidth) output)
        (combineBasis (allZeroAncilla p.ancillaWidth) input) =
      HistoryBlockEncoding.M09Bridge.encodedQComplexMatrix p output input /
        ((3 * p.K : Nat) : ℂ) := by
  have certificate := HistoryBlockEncoding.M09Bridge.recordedFullSpaceQ_success_block p
  let error : ProbabilityGeneratorQProof.Operator
      (RegisterBasis p.systemWidth) :=
    HistoryBlockEncoding.M09Bridge.encodedQComplexMatrix p -
      (((3 : ℝ) * (p.K : ℝ)) : ℂ) •
        qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
          (HistoryBlockEncoding.M09Bridge.recordedFullSpaceQ p)
  have upper : ‖error‖ ≤ 0 := by
    simpa [error] using certificate.2.2.2
  have normZero : ‖error‖ = 0 := by
    exact le_antisymm upper (norm_nonneg _)
  have matrixZero : error = 0 :=
    norm_eq_zero.mp normZero
  have entryZero :
      HistoryBlockEncoding.M09Bridge.encodedQComplexMatrix p output input -
        (((3 : ℝ) * (p.K : ℝ)) : ℂ) *
          HistoryBlockEncoding.M09Bridge.recordedFullSpaceQ p
            (combineBasis (allZeroAncilla p.ancillaWidth) output)
            (combineBasis (allZeroAncilla p.ancillaWidth) input) = 0 := by
    simpa [error, qubitSuccessBlock] using
      congrFun (congrFun matrixZero output) input
  have alphaNe : (((3 * p.K : Nat) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by decide : (3 : Nat) ≠ 0)
      (Nat.ne_of_gt p.K_pos))
  rw [show ((((3 : ℝ) * (p.K : ℝ)) : ℂ)) =
      ((3 * p.K : Nat) : ℂ) by norm_num] at entryZero
  apply (eq_div_iff alphaNe).2
  linear_combination -entryZero

def canonicalCoreSuccessBasis119
    (p : QParameters) (configuration : QConfiguration p) :
    QubitBasis (p.ancillaWidth + p.systemWidth) :=
  (jointBasisCoreEquiv p.ancillaWidth p.systemWidth)
    (combineBasis (allZeroAncilla p.ancillaWidth)
      (delimiterEncoding configuration))

theorem q10Recorded_core_success_entry119
    (p : QParameters) (output input : QConfiguration p) :
    reindexJointOperatorToCanonicalCore
        (q10ProbabilityGeneratorRecordedOperator p)
        (canonicalCoreSuccessBasis119 p output)
        (canonicalCoreSuccessBasis119 p input) =
      (HistoryBlockEncoding.QModel.configurationQMatrix output input : ℂ) /
        ((3 * p.K : Nat) : ℂ) := by
  rw [q10ProbabilityGeneratorRecordedOperator_eq_established]
  change HistoryBlockEncoding.M09Bridge.recordedFullSpaceQ p
      ((jointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
        (canonicalCoreSuccessBasis119 p output))
      ((jointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
        (canonicalCoreSuccessBasis119 p input)) = _
  simp only [canonicalCoreSuccessBasis119, Equiv.symm_apply_apply]
  rw [recordedFullSpaceQ_success_entry119]
  exact congrArg (fun value : ℂ => value / ((3 * p.K : Nat) : ℂ))
    (congrArg (fun value : ℚ => (value : ℂ))
      (HistoryBlockEncoding.M09Bridge.encodedQMatrix_entry output input))

end

end ExecutableHistoryExecutableHistory
