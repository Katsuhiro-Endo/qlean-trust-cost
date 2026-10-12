import QLean.Circuits.Foundation.WireEmbeddingAnalytic

namespace VerifiedCircuitCore

noncomputable section

/-- Euclidean action used by the pure wire-splitting layer. -/
def wireMatrixL2Action {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) :
    EuclideanSpace ℂ basis →ₗ[ℂ] EuclideanSpace ℂ basis :=
  Matrix.toLpLin 2 2 operator

def wireSplitL2IndexEquiv {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    QubitBasis targetQubits ≃
      Sigma (fun _ : OutsideWire placement → Bool => QubitBasis sourceQubits) :=
  (splitWireEmbeddingEquiv placement).trans
    ((Equiv.prodComm (QubitBasis sourceQubits)
      (OutsideWire placement → Bool)).trans
      (Equiv.sigmaEquivProd (OutsideWire placement → Bool)
        (QubitBasis sourceQubits)).symm)

def wireSplitL2Equiv {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    EuclideanSpace ℂ (QubitBasis targetQubits) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : OutsideWire placement → Bool =>
        EuclideanSpace ℂ (QubitBasis sourceQubits)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (wireSplitL2IndexEquiv placement)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2
      (fun _ : OutsideWire placement → Bool =>
        fun _ : QubitBasis sourceQubits => ℂ))

@[simp] theorem wireSplitL2Equiv_apply
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (state : EuclideanSpace ℂ (QubitBasis targetQubits))
    (outside : OutsideWire placement → Bool)
    (internal : QubitBasis sourceQubits) :
    (wireSplitL2Equiv placement state) outside internal =
      state (mergePlacedAndOutsideBasis placement internal outside) := by
  rfl

theorem wireSplitL2Equiv_wireMatrixL2Action_wireLiftOperator
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits))
    (state : EuclideanSpace ℂ (QubitBasis targetQubits)) :
    wireSplitL2Equiv placement
        (wireMatrixL2Action (wireLiftOperator placement operator) state) =
      WithLp.toLp 2 (fun outside =>
        wireMatrixL2Action operator
          ((wireSplitL2Equiv placement state) outside)) := by
  ext outside internal
  rw [wireSplitL2Equiv_apply]
  simp only [wireMatrixL2Action, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    Matrix.mulVec, wireLiftOperator, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  rw [show (splitWireEmbeddingEquiv placement)
      (mergePlacedAndOutsideBasis placement internal outside) =
        (internal, outside) by
    apply Prod.ext
    · exact restrictToPlacedWires_mergePlacedAndOutsideBasis
        placement internal outside
    · exact restrictToOutsideWires_mergePlacedAndOutsideBasis
        placement internal outside]
  change
    (∑ input : QubitBasis targetQubits,
      operator internal ((splitWireEmbeddingEquiv placement input).1) *
        (1 : Operator (OutsideWire placement → Bool)) outside
          ((splitWireEmbeddingEquiv placement input).2) * state input) =
      ∑ source : QubitBasis sourceQubits,
        operator internal source *
          state (mergePlacedAndOutsideBasis placement source outside)
  calc
    _ = ∑ pair : QubitBasis sourceQubits ×
          (OutsideWire placement → Bool),
        operator internal pair.1 *
          (1 : Operator (OutsideWire placement → Bool)) outside pair.2 *
          state ((splitWireEmbeddingEquiv placement).symm pair) := by
      apply Fintype.sum_equiv (splitWireEmbeddingEquiv placement)
      intro input
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [Matrix.one_apply, splitWireEmbeddingEquiv]

theorem piLpL2_norm_le_of_pointwise
    {index : Type*} [Fintype index]
    {fiber : index → Type*}
    [∀ i, SeminormedAddCommGroup (fiber i)]
    (actual target : PiLp 2 fiber) (error : ℝ)
    (errorNonnegative : 0 ≤ error)
    (pointwise : ∀ i, ‖actual i‖ ≤ error * ‖target i‖) :
    ‖actual‖ ≤ error * ‖target‖ := by
  have squaredPointwise : ∀ i,
      ‖actual i‖ ^ 2 ≤ error ^ 2 * ‖target i‖ ^ 2 := by
    intro i
    have bound := pointwise i
    nlinarith [norm_nonneg (actual i), norm_nonneg (target i)]
  have sumBound :
      (∑ i, ‖actual i‖ ^ 2) ≤
        error ^ 2 * ∑ i, ‖target i‖ ^ 2 := by
    calc
      (∑ i, ‖actual i‖ ^ 2) ≤
          ∑ i, error ^ 2 * ‖target i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => squaredPointwise i
      _ = error ^ 2 * ∑ i, ‖target i‖ ^ 2 := by
        rw [Finset.mul_sum]
  rw [← PiLp.norm_sq_eq_of_L2 fiber actual,
    ← PiLp.norm_sq_eq_of_L2 fiber target] at sumBound
  have productSquare :
      (error * ‖target‖) ^ 2 = error ^ 2 * ‖target‖ ^ 2 := by ring
  apply (sq_le_sq₀ (norm_nonneg actual)
    (mul_nonneg errorNonnegative (norm_nonneg target))).mp
  rw [productSquare]
  exact sumBound

theorem wireLiftOperator_sub {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (actual target : Operator (QubitBasis sourceQubits)) :
    wireLiftOperator placement (actual - target) =
      wireLiftOperator placement actual - wireLiftOperator placement target := by
  classical
  ext output input
  by_cases outsideEqual :
      restrictToOutsideWires placement output =
        restrictToOutsideWires placement input <;>
    simp [wireLiftOperator_apply, outsideEqual]

theorem wireLiftOperator_smul
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (scalar : ℂ) (operator : Operator (QubitBasis sourceQubits)) :
    wireLiftOperator placement (scalar • operator) =
      scalar • wireLiftOperator placement operator := by
  classical
  ext output input
  by_cases outsideEqual :
      restrictToOutsideWires placement output =
        restrictToOutsideWires placement input <;>
    simp [wireLiftOperator_apply, outsideEqual]

/-- Reindexing preserves unitarity, proved inside the pure wire layer. -/
private theorem wireReindex_mem_unitaryGroup
    {oldBasis newBasis : Type*}
    [Fintype oldBasis] [DecidableEq oldBasis]
    [Fintype newBasis] [DecidableEq newBasis]
    (equiv : oldBasis ≃ newBasis)
    {operator : Operator oldBasis}
    (unitary : operator ∈ Matrix.unitaryGroup oldBasis ℂ) :
    Matrix.reindex equiv equiv operator ∈ Matrix.unitaryGroup newBasis ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at unitary ⊢
  change Matrix.reindex equiv equiv operator *
      star (Matrix.reindex equiv equiv operator) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexLinearEquiv ℂ ℂ equiv equiv operator) *
      (Matrix.reindexLinearEquiv ℂ ℂ equiv equiv (star operator)) = 1
  rw [Matrix.reindexLinearEquiv_mul]
  have original : operator * star operator = 1 := unitary
  rw [original]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ equiv

/-- A unitary operator remains unitary after injective wire lifting. -/
theorem wireLiftOperator_mem_unitaryGroup
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    {operator : Operator (QubitBasis sourceQubits)}
    (unitary : operator ∈ Matrix.unitaryGroup (QubitBasis sourceQubits) ℂ) :
    wireLiftOperator placement operator ∈
      Matrix.unitaryGroup (QubitBasis targetQubits) ℂ := by
  unfold wireLiftOperator
  apply wireReindex_mem_unitaryGroup (splitWireEmbeddingEquiv placement).symm
  exact Matrix.kronecker_mem_unitary unitary (Submonoid.one_mem _)

end

end VerifiedCircuitCore
