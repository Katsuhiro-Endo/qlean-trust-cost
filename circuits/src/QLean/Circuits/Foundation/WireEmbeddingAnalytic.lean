import QLean.Circuits.Foundation.PrimitiveOperatorSemantics
import QLean.Circuits.Foundation.OperatorLocalityAnalytic

/-!
# injective wire 埋込みの回路非依存な解析意味論

狭い register の計算基底と、埋込み像の外側にある wire の計算基底を分離する。
この分離から、狭い作用素を外部 bit ごとの直和として広い register へ持ち上げる。
この module は回路構文木や回路 denotation を参照しない。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- injective wire 埋込みの像に含まれない外部 wire。 -/
def OutsideWire {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :=
  {wire : Fin targetQubits // ∀ source, placement source ≠ wire}

/-- 外部wire型は有限型である。 -/
noncomputable instance outsideWireFintype {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    Fintype (OutsideWire placement) :=
  Fintype.ofInjective (fun wire : OutsideWire placement => wire.1)
    Subtype.val_injective

/-- 外部wireの等号は有限wireの等号から決定できる。 -/
noncomputable instance outsideWireDecidableEq {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    DecidableEq (OutsideWire placement) :=
  Classical.decEq (OutsideWire placement)

/-- 広い計算基底から埋込み像上の内部 bit だけを読む。 -/
def restrictToPlacedWires {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (basis : QubitBasis targetQubits) : QubitBasis sourceQubits :=
  fun wire => basis (placement wire)

/-- 広い計算基底から埋込み像外の外部 bit だけを読む。 -/
def restrictToOutsideWires {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (basis : QubitBasis targetQubits) : OutsideWire placement → Bool :=
  fun wire => basis wire.1

/-- 内部基底と外部基底を一個の広い計算基底へ結合する。 -/
def mergePlacedAndOutsideBasis {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (internal : QubitBasis sourceQubits)
    (outside : OutsideWire placement → Bool) : QubitBasis targetQubits :=
  fun wire =>
    if existsSource : ∃ source, placement source = wire then
      internal (Classical.choose existsSource)
    else
      outside ⟨wire, fun source equal => existsSource ⟨source, equal⟩⟩

/-- 結合した基底を埋込み像上で読むと元の内部基底へ戻る。 -/
@[simp] theorem restrictToPlacedWires_mergePlacedAndOutsideBasis
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (internal : QubitBasis sourceQubits)
    (outside : OutsideWire placement → Bool) :
    restrictToPlacedWires placement
        (mergePlacedAndOutsideBasis placement internal outside) = internal := by
  funext source
  simp only [restrictToPlacedWires, mergePlacedAndOutsideBasis]
  split
  next existsSource =>
    have chosen : Classical.choose existsSource = source := by
      apply placement.injective
      exact Classical.choose_spec existsSource
    exact congrArg internal chosen
  next missing => exact False.elim (missing ⟨source, rfl⟩)

/-- 結合した基底を埋込み像外で読むと元の外部基底へ戻る。 -/
@[simp] theorem restrictToOutsideWires_mergePlacedAndOutsideBasis
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (internal : QubitBasis sourceQubits)
    (outside : OutsideWire placement → Bool) :
    restrictToOutsideWires placement
        (mergePlacedAndOutsideBasis placement internal outside) = outside := by
  funext wire
  simp [restrictToOutsideWires, mergePlacedAndOutsideBasis, wire.2]

/-- 広い基底を内部・外部へ分けて再結合すると元の基底へ戻る。 -/
@[simp] theorem mergePlacedAndOutsideBasis_restrict
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (basis : QubitBasis targetQubits) :
    mergePlacedAndOutsideBasis placement
        (restrictToPlacedWires placement basis)
        (restrictToOutsideWires placement basis) = basis := by
  funext wire
  simp only [mergePlacedAndOutsideBasis]
  split
  next existsSource =>
    simp [restrictToPlacedWires, Classical.choose_spec existsSource]
  next missing =>
    simp [restrictToOutsideWires]

/-- 広い基底を内部基底と外部基底へ分離する標準同値。 -/
def splitWireEmbeddingEquiv {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    QubitBasis targetQubits ≃
      QubitBasis sourceQubits × (OutsideWire placement → Bool) where
  toFun basis :=
    (restrictToPlacedWires placement basis,
      restrictToOutsideWires placement basis)
  invFun pair := mergePlacedAndOutsideBasis placement pair.1 pair.2
  left_inv := mergePlacedAndOutsideBasis_restrict placement
  right_inv pair := by
    apply Prod.ext
    · exact restrictToPlacedWires_mergePlacedAndOutsideBasis placement pair.1 pair.2
    · exact restrictToOutsideWires_mergePlacedAndOutsideBasis placement pair.1 pair.2

/-- 広い基底の等号は、内部制限と外部制限の二つの等号に分解できる。 -/
theorem fullBasis_eq_iff_restrictions_eq {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (left right : QubitBasis targetQubits) :
    left = right ↔
      restrictToPlacedWires placement left = restrictToPlacedWires placement right ∧
      restrictToOutsideWires placement left = restrictToOutsideWires placement right := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨internalEqual, outsideEqual⟩
    apply (splitWireEmbeddingEquiv placement).injective
    exact Prod.ext internalEqual outsideEqual

/-- 内部基底作用を行い外部bitを保存する広い基底作用。 -/
def liftBasisAction {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (action : QubitBasis sourceQubits → QubitBasis sourceQubits)
    (input : QubitBasis targetQubits) : QubitBasis targetQubits :=
  mergePlacedAndOutsideBasis placement
    (action (restrictToPlacedWires placement input))
    (restrictToOutsideWires placement input)

/-- 狭い作用素を、外部bitを保存する広い作用素へ回路非依存に持ち上げる。 -/
def wireLiftOperator {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    Operator (QubitBasis targetQubits) :=
  Matrix.reindex (splitWireEmbeddingEquiv placement).symm
    (splitWireEmbeddingEquiv placement).symm
    (Matrix.kronecker operator
      (1 : Operator (OutsideWire placement → Bool)))

/-- wire-liftの行列要素は内部作用素と外部基底保存deltaの積である。 -/
theorem wireLiftOperator_apply {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits))
    (output input : QubitBasis targetQubits) :
    wireLiftOperator placement operator output input =
      operator (restrictToPlacedWires placement output)
          (restrictToPlacedWires placement input) *
        if restrictToOutsideWires placement output =
            restrictToOutsideWires placement input then 1 else 0 := by
  classical
  rfl

/-- A lifted operator can change only wires in the image of its placement,
irrespective of the internal operator.  The outside Kronecker identity is the
entire reason for this locality statement. -/
theorem wireLiftOperator_preservesOutsidePlacement
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    OperatorPreservesOutside
      (Finset.univ.image placement)
      (wireLiftOperator placement operator) := by
  intro output input nonzero wire outside
  have wireOutside : ∀ source, placement source ≠ wire := by
    intro source equal
    apply outside
    exact Finset.mem_image.mpr ⟨source, Finset.mem_univ _, equal⟩
  have outsideEqual : restrictToOutsideWires placement output =
      restrictToOutsideWires placement input := by
    by_contra different
    rw [wireLiftOperator_apply, if_neg different, mul_zero] at nonzero
    exact nonzero rfl
  exact congrFun outsideEqual ⟨wire, wireOutside⟩

/-- 決定的内部基底作用のwire-liftは、外部bitを保存する決定的作用素である。 -/
theorem wireLiftOperator_deterministic {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (action : QubitBasis sourceQubits → QubitBasis sourceQubits) :
    wireLiftOperator placement (deterministicOperator action) =
      deterministicOperator (liftBasisAction placement action) := by
  classical
  ext output input
  rw [wireLiftOperator_apply]
  have outputEqualIff :
      output = liftBasisAction placement action input ↔
        restrictToPlacedWires placement output =
            action (restrictToPlacedWires placement input) ∧
          restrictToOutsideWires placement output =
            restrictToOutsideWires placement input := by
    rw [fullBasis_eq_iff_restrictions_eq placement]
    simp [liftBasisAction]
  by_cases internalEqual :
      restrictToPlacedWires placement output =
        action (restrictToPlacedWires placement input)
  · by_cases outsideEqual :
        restrictToOutsideWires placement output =
          restrictToOutsideWires placement input
    · simp [deterministicOperator, internalEqual, outsideEqual, outputEqualIff]
    · simp [deterministicOperator, internalEqual, outsideEqual, outputEqualIff]
  · simp [deterministicOperator, internalEqual, outputEqualIff]

/-- mapped targetのXOR更新を内部へ制限すると、元targetのXOR更新になる。 -/
theorem restrictToPlacedWires_xorWire {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (target : Fin sourceQubits) (value : Bool)
    (input : QubitBasis targetQubits) :
    restrictToPlacedWires placement
        (xorWire (placement target) value input) =
      xorWire target value (restrictToPlacedWires placement input) := by
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [restrictToPlacedWires, xorWire]
  · have mappedDifferent : placement wire ≠ placement target := by
      intro mappedEqual
      exact equal (placement.injective mappedEqual)
    simp [restrictToPlacedWires, xorWire, equal, mappedDifferent]

/-- XOR on a target wire outside the placement leaves the entire placed source
basis unchanged.  This is the pure locality fact used by surrounding
auxiliary predicates of an embedded component. -/
theorem restrictToPlacedWires_xorWire_outside
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (target : Fin targetQubits) (value : Bool)
    (input : QubitBasis targetQubits)
    (outside : ∀ source, target ≠ placement source) :
    restrictToPlacedWires placement (xorWire target value input) =
      restrictToPlacedWires placement input := by
  funext source
  simp [restrictToPlacedWires, xorWire, (outside source).symm]

/-- mapped targetのXOR更新は埋込み像外の全bitを保存する。 -/
theorem restrictToOutsideWires_xorWire {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (target : Fin sourceQubits) (value : Bool)
    (input : QubitBasis targetQubits) :
    restrictToOutsideWires placement
        (xorWire (placement target) value input) =
      restrictToOutsideWires placement input := by
  funext wire
  have different : wire.1 ≠ placement target := by
    intro equal
    exact wire.2 target equal.symm
  simp [restrictToOutsideWires, xorWire, different]

/-- 内部XOR作用の基底liftはmapped wire上のXOR作用と一致する。 -/
theorem liftBasisAction_xorWire {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (target : Fin sourceQubits)
    (value : QubitBasis sourceQubits → Bool)
    (input : QubitBasis targetQubits) :
    liftBasisAction placement
        (fun internal => xorWire target (value internal) internal) input =
      xorWire (placement target)
        (value (restrictToPlacedWires placement input)) input := by
  unfold liftBasisAction
  rw [← mergePlacedAndOutsideBasis_restrict placement
    (xorWire (placement target)
      (value (restrictToPlacedWires placement input)) input)]
  rw [restrictToPlacedWires_xorWire, restrictToOutsideWires_xorWire]

/-- global phaseのwire-liftは広いregister上の同じglobal phaseである。 -/
theorem wireLiftOperator_globalPhase {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) (angle : ℝ) :
    wireLiftOperator placement
        (globalPhaseOperator (basis := QubitBasis sourceQubits) angle) =
      globalPhaseOperator (basis := QubitBasis targetQubits) angle := by
  classical
  ext output input
  rw [wireLiftOperator_apply]
  have equalIff := fullBasis_eq_iff_restrictions_eq placement output input
  by_cases internalEqual :
      restrictToPlacedWires placement output =
        restrictToPlacedWires placement input
  · by_cases outsideEqual :
        restrictToOutsideWires placement output =
          restrictToOutsideWires placement input
    · have fullEqual : output = input := equalIff.2 ⟨internalEqual, outsideEqual⟩
      simp [globalPhaseOperator, fullEqual]
    · have fullDifferent : output ≠ input := by
        intro fullEqual
        exact outsideEqual (equalIff.1 fullEqual).2
      simp [globalPhaseOperator, internalEqual, outsideEqual, fullDifferent]
  · have fullDifferent : output ≠ input := by
      intro fullEqual
      exact internalEqual (equalIff.1 fullEqual).1
    simp [globalPhaseOperator, internalEqual, fullDifferent]

/-- 恒等作用素のwire-liftは広いregisterの恒等作用素である。 -/
@[simp] theorem wireLiftOperator_one {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    wireLiftOperator placement
        (1 : Operator (QubitBasis sourceQubits)) =
      (1 : Operator (QubitBasis targetQubits)) := by
  unfold wireLiftOperator
  calc
    Matrix.reindex (splitWireEmbeddingEquiv placement).symm
        (splitWireEmbeddingEquiv placement).symm
        (Matrix.kronecker 1 1) =
      Matrix.reindex (splitWireEmbeddingEquiv placement).symm
        (splitWireEmbeddingEquiv placement).symm 1 := by
          apply congrArg
          exact Matrix.one_kronecker_one
    _ = 1 :=
      (Matrix.reindexRingEquiv ℂ
        (splitWireEmbeddingEquiv placement).symm).map_one

/-- wire-liftは作用素積を保存する。 -/
theorem wireLiftOperator_mul {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (second first : Operator (QubitBasis sourceQubits)) :
    wireLiftOperator placement (second * first) =
      wireLiftOperator placement second * wireLiftOperator placement first := by
  unfold wireLiftOperator
  calc
    Matrix.reindex (splitWireEmbeddingEquiv placement).symm
        (splitWireEmbeddingEquiv placement).symm
        (Matrix.kronecker (second * first) 1) =
      Matrix.reindex (splitWireEmbeddingEquiv placement).symm
        (splitWireEmbeddingEquiv placement).symm
        (Matrix.kronecker (second * first) (1 * 1)) := by simp
    _ = Matrix.reindex (splitWireEmbeddingEquiv placement).symm
        (splitWireEmbeddingEquiv placement).symm
        (Matrix.kronecker second 1 * Matrix.kronecker first 1) := by
          apply congrArg
          exact Matrix.mul_kronecker_mul second first 1 1
    _ = Matrix.reindex (splitWireEmbeddingEquiv placement).symm
          (splitWireEmbeddingEquiv placement).symm
          (Matrix.kronecker second 1) *
        Matrix.reindex (splitWireEmbeddingEquiv placement).symm
          (splitWireEmbeddingEquiv placement).symm
          (Matrix.kronecker first 1) :=
      (Matrix.reindexRingEquiv ℂ
        (splitWireEmbeddingEquiv placement).symm).map_mul _ _

/-- wire-liftは作用素の自然数冪を保存する。 -/
theorem wireLiftOperator_pow {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    ∀ count : Nat,
      wireLiftOperator placement (operator ^ count) =
        wireLiftOperator placement operator ^ count
  | 0 => wireLiftOperator_one placement
  | count + 1 => by
      rw [pow_succ, pow_succ, wireLiftOperator_mul,
        wireLiftOperator_pow placement operator count]

/-- 内部基底と指定外部基底を結合する標準基底埋込み。 -/
def fixedOutsideBasisEmbedding {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool) :
    QubitBasis sourceQubits ↪ QubitBasis targetQubits where
  toFun internal := mergePlacedAndOutsideBasis placement internal outside
  inj' left right equal := by
    simpa using congrArg (restrictToPlacedWires placement) equal

/-- 内部状態を指定した外部計算基底のblockへ零拡張する解析的状態埋込み。 -/
def fixedOutsideStateEmbedding {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (state : State (QubitBasis sourceQubits)) :
    State (QubitBasis targetQubits) :=
  fun basis =>
    if restrictToOutsideWires placement basis = outside then
      state (restrictToPlacedWires placement basis)
    else 0

/-- 計算基底ketの状態埋込みは対応する広い計算基底ketそのものである。 -/
theorem fixedOutsideStateEmbedding_basisKet
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (input : QubitBasis sourceQubits) :
    fixedOutsideStateEmbedding placement outside (basisKet input) =
      basisKet (fixedOutsideBasisEmbedding placement outside input) := by
  funext basis
  simp only [fixedOutsideStateEmbedding, basisKet, fixedOutsideBasisEmbedding,
    VerifiedMath.Basis.vector, fullBasis_eq_iff_restrictions_eq placement]
  by_cases outsideEqual :
      restrictToOutsideWires placement basis = outside
  · by_cases internalEqual :
        restrictToPlacedWires placement basis = input
    · simp [outsideEqual, internalEqual]
    · simp [outsideEqual, internalEqual]
  · simp [outsideEqual]

/-- 固定外部基底を持つ広い計算基底であるという独立なpredicate。 -/
def HasFixedOutsideBasis {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (basis : QubitBasis targetQubits) : Prop :=
  restrictToOutsideWires placement basis = outside

/-- 標準埋込みで作った基底は指定した外部基底を持つ。 -/
@[simp] theorem fixedOutsideBasisEmbedding_hasFixedOutsideBasis
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (internal : QubitBasis sourceQubits) :
    HasFixedOutsideBasis placement outside
      (fixedOutsideBasisEmbedding placement outside internal) := by
  exact restrictToOutsideWires_mergePlacedAndOutsideBasis placement internal outside

end

end VerifiedCircuitCore
