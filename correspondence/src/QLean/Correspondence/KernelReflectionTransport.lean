import QLean.MathematicalSpecifications.KernelReflection
import QLean.Correspondence.HistoryLinearSystemTransport
import QLean.History.Jennings.M13

/-!
# Kernel-reflection representation transport

The ideal reflection is defined independently on the mathematical state
alphabet.  This file proves that the legacy finite-numbered implementation
target is exactly its simultaneous row/column reindexing.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Correspondence.KernelReflectionTransport

open Matrix
open scoped BigOperators
open QLean.MathematicalSpecifications

noncomputable section

def extendedIndexEquiv {state : Type*}
    {d clockCount orderCount : Nat} (stateEquiv : state ≃ Fin d) :
    KernelReflection.ExtendedIndex state clockCount orderCount ≃
      GramOperator.ExtendedIndex d clockCount orderCount :=
  Equiv.sumCongr
    (HistoryLinearSystemTransport.indexEquiv
      (clockCount := clockCount) (orderCount := orderCount) stateEquiv)
    (Equiv.refl Unit)

theorem reindex_mulVec_apply
    {source target : Type*} [Fintype source] [Fintype target]
    [DecidableEq source] [DecidableEq target]
    (equivalence : source ≃ target)
    (matrix : Matrix source source ℝ) (vector : source → ℝ)
    (index : source) :
    (Matrix.reindex equivalence equivalence matrix).mulVec
        (fun targetIndex => vector (equivalence.symm targetIndex))
        (equivalence index) =
      matrix.mulVec vector index := by
  rw [Matrix.reindex_apply]
  unfold Matrix.mulVec dotProduct
  rw [← equivalence.sum_comp]
  simp

theorem historyOperator_eq_reindex
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) :
    JenningsHistory.historyMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data) =
      Matrix.reindexAlgEquiv ℝ ℝ
        (HistoryLinearSystemTransport.indexEquiv
          (clockCount := clockCount) (orderCount := orderCount) stateEquiv)
        (HistoryLinearSystem.operator data.toMatrixData) := by
  let equivalence :
      HistoryLinearSystem.Index state clockCount orderCount ≃
        JenningsHistory.HistoryIndex d clockCount orderCount :=
    HistoryLinearSystemTransport.indexEquiv stateEquiv
  funext row column
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  simpa [equivalence] using
    HistoryLinearSystemTransport.operator_entry_transport stateEquiv data
      (equivalence.symm row) (equivalence.symm column)

theorem rightHandSideNorm_transport
    {state : Type*} [Fintype state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) :
    JenningsHistory.rhsNorm
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data) =
      KernelReflection.rightHandSideNorm data := by
  let equivalence :
      HistoryLinearSystem.Index state clockCount orderCount ≃
        JenningsHistory.HistoryIndex d clockCount orderCount :=
    HistoryLinearSystemTransport.indexEquiv stateEquiv
  unfold JenningsHistory.rhsNorm JenningsHistory.rhsNormSq
    KernelReflection.rightHandSideNorm VerifiedMath.FiniteReal.normSquared
  congr 1
  calc
    (∑ index,
        JenningsHistory.historyRhs
            (HistoryLinearSystemTransport.toCircuitData stateEquiv data) index *
          JenningsHistory.historyRhs
            (HistoryLinearSystemTransport.toCircuitData stateEquiv data) index) =
        ∑ index, JenningsHistory.historyRhs
            (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              (equivalence index) *
          JenningsHistory.historyRhs
            (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              (equivalence index) := by
          symm
          exact equivalence.sum_comp (fun targetIndex =>
            JenningsHistory.historyRhs
                (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                targetIndex *
              JenningsHistory.historyRhs
                (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                targetIndex)
    _ = ∑ index, HistoryLinearSystem.rightHandSide data index *
          HistoryLinearSystem.rightHandSide data index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [HistoryLinearSystemTransport.rightHandSide_entry_transport]

theorem normalizedRightHandSide_transport
    {state : Type*} [Fintype state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (index : HistoryLinearSystem.Index state clockCount orderCount) :
    JenningsHistory.normalizedRhs
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        (HistoryLinearSystemTransport.indexEquiv
          (clockCount := clockCount) (orderCount := orderCount)
          stateEquiv index) =
      KernelReflection.normalizedRightHandSide data index := by
  rw [KernelReflection.normalizedRightHandSide_eq_quotient]
  unfold JenningsHistory.normalizedRhs
  rw [HistoryLinearSystemTransport.rightHandSide_entry_transport,
    rightHandSideNorm_transport]

theorem extendedOperator_eq_reindex
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ) :
    GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu =
      Matrix.reindexAlgEquiv ℝ ℝ (extendedIndexEquiv
        (clockCount := clockCount) (orderCount := orderCount) stateEquiv)
        (KernelReflection.extendedOperator data alpha nu) := by
  let equivalence :
      KernelReflection.ExtendedIndex state clockCount orderCount ≃
        GramOperator.ExtendedIndex d clockCount orderCount :=
    extendedIndexEquiv stateEquiv
  funext row column
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  cases row with
  | inl row => cases column with
    | inl column =>
      change JenningsHistory.historyMatrix
          (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
            row column / alpha =
        HistoryLinearSystem.operator data.toMatrixData
            ((HistoryLinearSystemTransport.indexEquiv stateEquiv).symm row)
            ((HistoryLinearSystemTransport.indexEquiv stateEquiv).symm column) /
          alpha
      congr 1
      simpa using HistoryLinearSystemTransport.operator_entry_transport
        stateEquiv data
          ((HistoryLinearSystemTransport.indexEquiv stateEquiv).symm row)
          ((HistoryLinearSystemTransport.indexEquiv stateEquiv).symm column)
    | inr value => cases value; rfl
  | inr value =>
      cases value
      cases column with
      | inl column =>
          simp [GramOperator.enlargedMatrix, JenningsHistory.dalzellExtendedH,
            KernelReflection.extendedOperator, extendedIndexEquiv]
      | inr value =>
          cases value
          simp [GramOperator.enlargedMatrix, JenningsHistory.dalzellExtendedH,
            KernelReflection.extendedOperator, extendedIndexEquiv]

theorem bPlus_transport
    {state : Type*} [Fintype state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount)
    (index : KernelReflection.ExtendedIndex state clockCount orderCount) :
    GramOperator.bPlus
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        (extendedIndexEquiv (clockCount := clockCount)
          (orderCount := orderCount) stateEquiv index) =
      KernelReflection.bPlus data index := by
  cases index with
  | inl index =>
      change JenningsHistory.normalizedRhs
          (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
          (HistoryLinearSystemTransport.indexEquiv stateEquiv index) /
          Real.sqrt 2 =
        KernelReflection.normalizedRightHandSide data index / Real.sqrt 2
      rw [normalizedRightHandSide_transport]
  | inr value => cases value; rfl

theorem extendedOperator_det_transport
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ) :
    (GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu).det =
      (KernelReflection.extendedOperator data alpha nu).det := by
  rw [extendedOperator_eq_reindex, Matrix.coe_reindexAlgEquiv,
    Matrix.det_reindex_self]

/-- Invertibility also transports from the finite-numbered implementation
back to the independently named mathematical state space.  No new
invertibility premise is introduced: the determinant is unchanged by the
simultaneous row/column reindexing. -/
theorem independentInvertibility
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ)
    (invertible : IsUnit
      (GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu).det) :
    IsUnit (KernelReflection.extendedOperator data alpha nu).det := by
  rw [← extendedOperator_det_transport stateEquiv data alpha nu]
  exact invertible

theorem kernelVector_transport
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ)
    (circuitInvertible : IsUnit
      (GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu).det)
    (invertible : IsUnit (KernelReflection.extendedOperator data alpha nu).det)
    (index : KernelReflection.ExtendedIndex state clockCount orderCount) :
    GramOperator.m13KernelVector
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu circuitInvertible
        (extendedIndexEquiv (clockCount := clockCount)
          (orderCount := orderCount) stateEquiv index) =
      KernelReflection.kernelVector data alpha nu invertible index := by
  let equivalence :
      KernelReflection.ExtendedIndex state clockCount orderCount ≃
        GramOperator.ExtendedIndex d clockCount orderCount :=
    extendedIndexEquiv stateEquiv
  have bEquality :
      GramOperator.bPlus
          (HistoryLinearSystemTransport.toCircuitData stateEquiv data) =
        fun targetIndex =>
          KernelReflection.bPlus data (equivalence.symm targetIndex) := by
    funext targetIndex
    obtain ⟨sourceIndex, rfl⟩ := equivalence.surjective targetIndex
    simpa [equivalence] using bPlus_transport stateEquiv data sourceIndex
  unfold GramOperator.m13KernelVector KernelReflection.kernelVector
  rw [extendedOperator_eq_reindex, Matrix.coe_reindexAlgEquiv,
    Matrix.inv_reindex, bEquality]
  exact reindex_mulVec_apply equivalence
    (KernelReflection.extendedOperator data alpha nu)⁻¹
    (KernelReflection.bPlus data) index

theorem normalizedKernel_transport
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ)
    (circuitInvertible : IsUnit
      (GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu).det)
    (invertible : IsUnit (KernelReflection.extendedOperator data alpha nu).det)
    (index : KernelReflection.ExtendedIndex state clockCount orderCount) :
    GramOperator.gHat
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu circuitInvertible
        (extendedIndexEquiv (clockCount := clockCount)
          (orderCount := orderCount) stateEquiv index) =
      KernelReflection.normalizedKernel data alpha nu invertible index := by
  let equivalence :
      KernelReflection.ExtendedIndex state clockCount orderCount ≃
        GramOperator.ExtendedIndex d clockCount orderCount :=
    extendedIndexEquiv stateEquiv
  have normEquality :
      JenningsHistory.unitNormSquared
          (GramOperator.m13KernelVector
            (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
            alpha nu circuitInvertible) =
        KernelReflection.normSquared
          (KernelReflection.kernelVector data alpha nu invertible) := by
    unfold JenningsHistory.unitNormSquared KernelReflection.normSquared
    calc
      (∑ targetIndex,
          GramOperator.m13KernelVector
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              targetIndex *
            GramOperator.m13KernelVector
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              targetIndex) =
          ∑ sourceIndex,
            GramOperator.m13KernelVector
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              (equivalence sourceIndex) *
            GramOperator.m13KernelVector
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              (equivalence sourceIndex) := by
            symm
            exact equivalence.sum_comp (fun targetIndex =>
              GramOperator.m13KernelVector
                  (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                  alpha nu circuitInvertible targetIndex *
                GramOperator.m13KernelVector
                  (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                  alpha nu circuitInvertible targetIndex)
      _ = ∑ sourceIndex,
          KernelReflection.kernelVector data alpha nu invertible sourceIndex *
            KernelReflection.kernelVector data alpha nu invertible sourceIndex := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        have pointwise :
            GramOperator.m13KernelVector
                (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                alpha nu circuitInvertible (equivalence sourceIndex) =
              KernelReflection.kernelVector data alpha nu invertible
                sourceIndex := by
          simpa [equivalence] using
            kernelVector_transport stateEquiv data alpha nu circuitInvertible
              invertible sourceIndex
        rw [pointwise]
  unfold GramOperator.gHat GramOperator.normalizedVector
    KernelReflection.normalizedKernel
    VerifiedMath.FiniteReal.normalize
  rw [normEquality]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [kernelVector_transport stateEquiv data alpha nu circuitInvertible
    invertible]
  rfl

theorem idealReflection_entry_transport
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ)
    (circuitInvertible : IsUnit
      (GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu).det)
    (invertible : IsUnit (KernelReflection.extendedOperator data alpha nu).det)
    (row column : KernelReflection.ExtendedIndex state clockCount orderCount) :
    GramOperator.idealKernelReflection
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu circuitInvertible
        (extendedIndexEquiv (clockCount := clockCount)
          (orderCount := orderCount) stateEquiv row)
        (extendedIndexEquiv (clockCount := clockCount)
          (orderCount := orderCount) stateEquiv column) =
      KernelReflection.idealReflection data alpha nu invertible row column := by
  unfold GramOperator.idealKernelReflection JenningsHistory.kernelReflection
    JenningsHistory.kernelProjector
    KernelReflection.idealReflection
    VerifiedMath.FiniteReal.lineProjector VerifiedMath.FiniteReal.normSquared
  simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply]
  simp only [normalizedKernel_transport stateEquiv data alpha nu
    circuitInvertible invertible row,
    normalizedKernel_transport stateEquiv data alpha nu circuitInvertible
      invertible column]
  have denominatorEquality :
      (∑ index,
          GramOperator.gHat
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              index *
            GramOperator.gHat
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              index) =
        ∑ index,
          KernelReflection.normalizedKernel data alpha nu invertible index *
            KernelReflection.normalizedKernel data alpha nu invertible index := by
    let equivalence :
        KernelReflection.ExtendedIndex state clockCount orderCount ≃
          GramOperator.ExtendedIndex d clockCount orderCount :=
      extendedIndexEquiv stateEquiv
    calc
      (∑ targetIndex,
          GramOperator.gHat
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              targetIndex *
            GramOperator.gHat
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              targetIndex) =
          ∑ sourceIndex,
            GramOperator.gHat
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              (equivalence sourceIndex) *
            GramOperator.gHat
              (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
              alpha nu circuitInvertible
              (equivalence sourceIndex) := by
            symm
            exact equivalence.sum_comp (fun targetIndex =>
              GramOperator.gHat
                  (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                  alpha nu circuitInvertible targetIndex *
                GramOperator.gHat
                  (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                  alpha nu circuitInvertible targetIndex)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        have pointwise :
            GramOperator.gHat
                (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
                alpha nu circuitInvertible (equivalence sourceIndex) =
              KernelReflection.normalizedKernel data alpha nu invertible
                sourceIndex := by
          simpa [equivalence] using
            normalizedKernel_transport stateEquiv data alpha nu
              circuitInvertible invertible sourceIndex
        rw [pointwise]
  rw [denominatorEquality]
  simp

/-- Exact operator-level statement used by the QSVT correspondence. -/
theorem idealReflection_eq_reindex
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount) (alpha nu : ℝ)
    (circuitInvertible : IsUnit
      (GramOperator.enlargedMatrix
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu).det)
    (invertible : IsUnit (KernelReflection.extendedOperator data alpha nu).det) :
    GramOperator.idealKernelReflection
        (HistoryLinearSystemTransport.toCircuitData stateEquiv data)
        alpha nu circuitInvertible =
      Matrix.reindexAlgEquiv ℝ ℝ (extendedIndexEquiv
        (clockCount := clockCount) (orderCount := orderCount) stateEquiv)
        (KernelReflection.idealReflection data alpha nu invertible) := by
  let equivalence :
      KernelReflection.ExtendedIndex state clockCount orderCount ≃
        GramOperator.ExtendedIndex d clockCount orderCount :=
    extendedIndexEquiv stateEquiv
  funext row column
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  simpa [equivalence] using
    idealReflection_entry_transport stateEquiv data alpha nu
      circuitInvertible invertible (equivalence.symm row)
        (equivalence.symm column)

/-- A dependency-friendly form of `idealReflection_eq_reindex`.  It permits a
caller to identify its circuit-side history data with the transported
independent data without unfolding a large concrete record during rewriting. -/
theorem idealReflection_eq_reindex_of_data_eq
    {state : Type*} [Fintype state] [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : HistoryLinearSystem.Data state clockCount taylorOrder physicalSteps
      orderCount)
    (circuitData : JenningsHistory.HistorySpec d clockCount taylorOrder
      physicalSteps orderCount)
    (alpha nu : ℝ)
    (data_eq : circuitData =
      HistoryLinearSystemTransport.toCircuitData stateEquiv data)
    (circuitInvertible : IsUnit
      (GramOperator.enlargedMatrix circuitData alpha nu).det)
    (invertible : IsUnit (KernelReflection.extendedOperator data alpha nu).det) :
    GramOperator.idealKernelReflection circuitData alpha nu circuitInvertible =
      Matrix.reindexAlgEquiv ℝ ℝ (extendedIndexEquiv
        (clockCount := clockCount) (orderCount := orderCount) stateEquiv)
        (KernelReflection.idealReflection data alpha nu invertible) := by
  subst circuitData
  exact idealReflection_eq_reindex stateEquiv data alpha nu
    circuitInvertible invertible

end

end QLean.Correspondence.KernelReflectionTransport
