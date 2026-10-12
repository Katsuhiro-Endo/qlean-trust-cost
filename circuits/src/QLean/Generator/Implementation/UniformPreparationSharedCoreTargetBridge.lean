import QLean.Generator.Implementation.UniformPreparationSharedCoreAdapter
import QLean.Generator.Analysis.UniformPreparationQLayout

/-!
# 共有一様準備 target と Q レイアウト解析状態の橋

共有 core component が返す固定外部 wire 状態を、Q の selector レイアウト上で使う
解析状態へ同定する。ここでは回路の意味論を使わず、二つの状態定義だけを比較する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 共有 component の target field を展開した標準形。 -/
theorem frozenUniformPreparationOnJointBasisComponent_targetState
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (frozenUniformPreparationOnJointBasisComponent p selectorWire
      selectorInjective selectorScratchDisjoint background).targetState =
      reindexCanonicalCoreStateToJoint
        (VerifiedCircuitCore.fixedOutsideStateEmbedding
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint)
          (sharedUniformOutsideBasis p selectorWire selectorInjective
            selectorScratchDisjoint background)
          (VerifiedCircuitCore.uniformPreparationFullTargetState
            (sharedUniformPreparationParameters p))) := by
  rfl

/-- 共有 component の initial field を展開した標準形。 -/
theorem frozenUniformPreparationOnJointBasisComponent_initialState
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    (frozenUniformPreparationOnJointBasisComponent p selectorWire
      selectorInjective selectorScratchDisjoint background).initialState =
      reindexCanonicalCoreStateToJoint
        (VerifiedCircuitCore.basisKet
          (VerifiedCircuitCore.fixedOutsideBasisEmbedding
            (sharedUniformCorePlacement p selectorWire selectorInjective
              selectorScratchDisjoint)
            (sharedUniformOutsideBasis p selectorWire selectorInjective
              selectorScratchDisjoint background)
            (VerifiedCircuitCore.zeroUniformPreparationBasis p.selectorWidth))) := by
  rfl

/-- 共有 placement の前半は Q selector bit を読む。 -/
@[simp] theorem restrictSharedUniformPlacement_selector
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (index : Fin p.selectorWidth) :
    VerifiedCircuitCore.restrictToPlacedWires
        (sharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint)
        (jointBasisToCore basis)
        ⟨index.val, by omega⟩ =
      basis (selectorWire index) := by
  simp [VerifiedCircuitCore.restrictToPlacedWires,
    sharedUniformCorePlacement, sharedUniformLocalWire, index.isLt]

/-- 共有 placement の後半は Q の一様準備 scratch bit を読む。 -/
@[simp] theorem restrictSharedUniformPlacement_scratch
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (index : Fin p.selectorWidth) :
    VerifiedCircuitCore.restrictToPlacedWires
        (sharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint)
        (jointBasisToCore basis)
        ⟨p.selectorWidth + index.val, by omega⟩ =
      basis (sharedUniformScratchWire p index) := by
  simp [VerifiedCircuitCore.restrictToPlacedWires,
    sharedUniformCorePlacement, sharedUniformLocalWire]

/-- 共有 placement から抽出した local selector は Q の selector 射影である。 -/
theorem sharedUniformSelectorBasis_restrict_eq_project
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.uniformPreparationSelectorBasis p.selectorWidth
        (VerifiedCircuitCore.restrictToPlacedWires
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint)
          (jointBasisToCore basis)) =
      projectSelectorBasis p selectorWire basis := by
  funext index
  exact restrictSharedUniformPlacement_selector p selectorWire
    selectorInjective selectorScratchDisjoint basis index

/-- local scratch の全零条件は、Q に配置した共有 scratch の全零条件である。 -/
theorem sharedUniformScratchZero_restrict_iff
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.uniformPreparationScratchZero p.selectorWidth
        (VerifiedCircuitCore.restrictToPlacedWires
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint)
          (jointBasisToCore basis)) ↔
      ∀ index : Fin p.selectorWidth,
        basis (sharedUniformScratchWire p index) = false := by
  constructor
  · intro scratchZero index
    simpa only [restrictSharedUniformPlacement_scratch] using scratchZero index
  · intro scratchZero index
    simpa only [restrictSharedUniformPlacement_scratch] using scratchZero index

/--
selector と共有 scratch が背景上で全零なら、共有 placement の全零 internal basis と
背景 outside basis を併合した結果は背景 basis そのものである。
-/
theorem fixedOutsideZeroUniformBasis_eq_background
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorZero : ∀ index, background (selectorWire index) = false)
    (scratchZero : ∀ index,
      background (sharedUniformScratchWire p index) = false) :
    VerifiedCircuitCore.fixedOutsideBasisEmbedding
        (sharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint)
        (sharedUniformOutsideBasis p selectorWire selectorInjective
          selectorScratchDisjoint background)
        (VerifiedCircuitCore.zeroUniformPreparationBasis p.selectorWidth) =
      jointBasisToCore background := by
  change VerifiedCircuitCore.mergePlacedAndOutsideBasis
      (sharedUniformCorePlacement p selectorWire selectorInjective
        selectorScratchDisjoint)
      (VerifiedCircuitCore.zeroUniformPreparationBasis p.selectorWidth)
      (sharedUniformOutsideBasis p selectorWire selectorInjective
        selectorScratchDisjoint background) =
    jointBasisToCore background
  apply (VerifiedCircuitCore.fullBasis_eq_iff_restrictions_eq
    (sharedUniformCorePlacement p selectorWire selectorInjective
      selectorScratchDisjoint) _ _).mpr
  constructor
  · rw [VerifiedCircuitCore.restrictToPlacedWires_mergePlacedAndOutsideBasis]
    funext source
    simp only [VerifiedCircuitCore.zeroUniformPreparationBasis,
      VerifiedCircuitCore.restrictToPlacedWires, sharedUniformCorePlacement]
    by_cases sourceSelector : source.val < p.selectorWidth
    · change false = jointBasisToCore background
        (wireToCanonicalFin (sharedUniformLocalWire p selectorWire source))
      rw [jointBasisToCore_wireToCanonicalFin,
        show sharedUniformLocalWire p selectorWire source =
          selectorWire ⟨source.val, sourceSelector⟩ by
        simp [sharedUniformLocalWire, sourceSelector]]
      exact (selectorZero ⟨source.val, sourceSelector⟩).symm
    · let index : Fin p.selectorWidth :=
        ⟨source.val - p.selectorWidth, by omega⟩
      change false = jointBasisToCore background
        (wireToCanonicalFin (sharedUniformLocalWire p selectorWire source))
      rw [jointBasisToCore_wireToCanonicalFin,
        show sharedUniformLocalWire p selectorWire source =
          sharedUniformScratchWire p index by
        simp [sharedUniformLocalWire, sourceSelector, index]]
      exact (scratchZero index).symm
  · rw [VerifiedCircuitCore.restrictToOutsideWires_mergePlacedAndOutsideBasis]
    rfl

/-- selector/scratch 全零の背景では共有 component の初期状態はその背景 ket である。 -/
theorem frozenUniformPreparationOnJointBasisComponent_initialState_eq_basisKet
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorZero : ∀ index, background (selectorWire index) = false)
    (scratchZero : ∀ index,
      background (sharedUniformScratchWire p index) = false) :
    (frozenUniformPreparationOnJointBasisComponent p selectorWire
      selectorInjective selectorScratchDisjoint background).initialState =
      VerifiedCircuitCore.basisKet background := by
  rw [frozenUniformPreparationOnJointBasisComponent_initialState,
    fixedOutsideZeroUniformBasis_eq_background p selectorWire selectorInjective
      selectorScratchDisjoint background selectorZero scratchZero]
  funext basis
  unfold reindexCanonicalCoreStateToJoint VerifiedCircuitCore.basisKet
  by_cases equal : basis = background
  · subst basis
    simp
  · have coreDifferent :
        jointBasisToCore basis ≠ jointBasisToCore background := by
      intro coreEqual
      exact equal ((jointBasisCoreEquiv p.ancillaWidth p.systemWidth).injective
        coreEqual)
    simp [coreDifferent, equal]

/-- selector と共有 scratch のどちらにも配置されない Q wire 上で背景と一致する条件。 -/
def OutsideSharedUniformPlacementMatches
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire,
    (∀ source : Fin (2 * p.selectorWidth),
      sharedUniformLocalWire p selectorWire source ≠ wire) →
    basis wire = background wire

/-- core の outside-wire 等式を、Q wire 上の配置外一致条件へ移す。 -/
theorem restrictSharedUniformOutside_eq_iff
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background basis : JointBasis p.ancillaWidth p.systemWidth) :
    VerifiedCircuitCore.restrictToOutsideWires
        (sharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint)
        (jointBasisToCore basis) =
      sharedUniformOutsideBasis p selectorWire selectorInjective
        selectorScratchDisjoint background ↔
      OutsideSharedUniformPlacementMatches p selectorWire background basis := by
  constructor
  · intro outsideEqual wire wireOutside
    have coreOutside : ∀ source : Fin (2 * p.selectorWidth),
        sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint source ≠ wireToCanonicalFin wire := by
      intro source equal
      apply wireOutside source
      apply wireToCanonicalFin_injective
      simpa [sharedUniformCorePlacement] using equal
    have pointwise := congrFun outsideEqual
      (⟨wireToCanonicalFin wire, coreOutside⟩ :
        VerifiedCircuitCore.OutsideWire
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint))
    simpa [VerifiedCircuitCore.restrictToOutsideWires,
      sharedUniformOutsideBasis] using pointwise
  · intro outsideMatch
    funext outsideWire
    apply outsideMatch (canonicalFinToWire outsideWire.1)
    intro source equal
    apply outsideWire.2 source
    change wireToCanonicalFin (sharedUniformLocalWire p selectorWire source) =
      outsideWire.1
    rw [equal, wireToCanonicalFin_canonicalFinToWire]

/--
背景の一様準備 scratch が全零なら、Q の「selector 外で背景と一致」は、
共有 placement 外の一致と local scratch 全零へちょうど分解できる。
-/
theorem outsideSelectorMatches_iff_sharedPlacement_and_scratchZero
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background basis : JointBasis p.ancillaWidth p.systemWidth)
    (backgroundScratchZero : ∀ wire ∈ uniformScratchWires p,
      background wire = false) :
    OutsideSelectorMatches p selectorWire background basis ↔
      OutsideSharedUniformPlacementMatches p selectorWire background basis ∧
        ∀ index : Fin p.selectorWidth,
          basis (sharedUniformScratchWire p index) = false := by
  constructor
  · intro outsideSelector
    constructor
    · intro wire localOutside
      apply outsideSelector wire
      intro selectorMember
      rcases List.mem_map.mp selectorMember with ⟨index, _, rfl⟩
      apply localOutside ⟨index.val, by omega⟩
      simp [sharedUniformLocalWire, index.isLt]
    · intro index
      have scratchMember :=
        sharedUniformScratchWire_mem_uniformScratchWires p index
      have scratchNotSelector :
          sharedUniformScratchWire p index ∉
            (List.finRange p.selectorWidth).map selectorWire := by
        intro selectorMember
        exact (List.disjoint_left.mp selectorScratchDisjoint)
          selectorMember scratchMember
      rw [outsideSelector _ scratchNotSelector]
      exact backgroundScratchZero _ scratchMember
  · rintro ⟨outsideShared, scratchZero⟩ wire wireNotSelector
    by_cases placed : ∃ source : Fin (2 * p.selectorWidth),
        sharedUniformLocalWire p selectorWire source = wire
    · rcases placed with ⟨source, rfl⟩
      by_cases sourceSelector : source.val < p.selectorWidth
      · exfalso
        apply wireNotSelector
        apply List.mem_map.mpr
        exact ⟨⟨source.val, sourceSelector⟩, List.mem_finRange _, by
          simp [sharedUniformLocalWire, sourceSelector]⟩
      · let index : Fin p.selectorWidth :=
          ⟨source.val - p.selectorWidth, by omega⟩
        have sourceIsScratch :
            sharedUniformLocalWire p selectorWire source =
              sharedUniformScratchWire p index := by
          simp [sharedUniformLocalWire, sourceSelector, index]
        rw [sourceIsScratch, scratchZero index]
        symm
        exact backgroundScratchZero _
          (sharedUniformScratchWire_mem_uniformScratchWires p index)
    · exact outsideShared wire (by simpa only [not_exists] using placed)

/-- Q と共有 core の little-endian selector 復号値は一致する。 -/
theorem coreSelectorValue_eq_qSelectorValue :
    ∀ (width : Nat) (basis : AbstractSelectorBasis width),
      VerifiedCircuitCore.selectorValue width basis = selectorValue width basis
  | _, _ => rfl

/-- Q 側に残す解析 selector state は共有 core の同じ解析式と一致する。 -/
theorem coreIdealUniformSelectorState_eq_qIdeal
    (width validCount : Nat) :
    VerifiedCircuitCore.idealUniformSelectorState width validCount =
      idealUniformSelectorState width validCount := by
  rfl

/--
共有 core component の独立 target は、scratch 全零の Q 背景上で従来の
`liftSelectorStateOver` 解析式と一致する。
-/
theorem frozenUniformPreparationOnJointBasisComponent_targetState_eq_liftSelectorStateOver
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (backgroundScratchZero : ∀ wire ∈ uniformScratchWires p,
      background wire = false) :
    (frozenUniformPreparationOnJointBasisComponent p selectorWire
      selectorInjective selectorScratchDisjoint background).targetState =
      liftSelectorStateOver p selectorWire background
        (idealUniformSelectorState p.selectorWidth p.selectorCount) := by
  classical
  rw [frozenUniformPreparationOnJointBasisComponent_targetState]
  funext basis
  change
    (if VerifiedCircuitCore.restrictToOutsideWires
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint)
          (jointBasisToCore basis) =
        sharedUniformOutsideBasis p selectorWire selectorInjective
          selectorScratchDisjoint background then
      (if VerifiedCircuitCore.uniformPreparationScratchZero p.selectorWidth
          (VerifiedCircuitCore.restrictToPlacedWires
            (sharedUniformCorePlacement p selectorWire selectorInjective
              selectorScratchDisjoint)
            (jointBasisToCore basis)) then
        VerifiedCircuitCore.uniformPreparationTargetState
          (sharedUniformPreparationParameters p)
          (VerifiedCircuitCore.uniformPreparationSelectorBasis p.selectorWidth
            (VerifiedCircuitCore.restrictToPlacedWires
              (sharedUniformCorePlacement p selectorWire selectorInjective
                selectorScratchDisjoint)
              (jointBasisToCore basis)))
      else 0)
    else 0) =
      (if OutsideSelectorMatches p selectorWire background basis then
        idealUniformSelectorState p.selectorWidth p.selectorCount
          (projectSelectorBasis p selectorWire basis)
      else 0)
  have outsideIff := restrictSharedUniformOutside_eq_iff p selectorWire
    selectorInjective selectorScratchDisjoint background basis
  have scratchIff := sharedUniformScratchZero_restrict_iff p selectorWire
    selectorInjective selectorScratchDisjoint basis
  have selectorIff :=
    outsideSelectorMatches_iff_sharedPlacement_and_scratchZero p selectorWire
      selectorScratchDisjoint background basis backgroundScratchZero
  by_cases outsideSelector : OutsideSelectorMatches p selectorWire background basis
  · rcases selectorIff.mp outsideSelector with ⟨outsideShared, scratchZero⟩
    rw [if_pos (outsideIff.mpr outsideShared), if_pos (scratchIff.mpr scratchZero),
      if_pos outsideSelector,
      sharedUniformSelectorBasis_restrict_eq_project]
    rw [← coreIdealUniformSelectorState_eq_qIdeal]
    simpa [sharedUniformPreparationParameters] using
      (congrFun
        (VerifiedCircuitCore.idealUniformSelectorState_eq_uniformPreparationTargetState
          (sharedUniformPreparationParameters p))
        (projectSelectorBasis p selectorWire basis)).symm
  · rw [if_neg outsideSelector]
    by_cases outsideCore :
        VerifiedCircuitCore.restrictToOutsideWires
            (sharedUniformCorePlacement p selectorWire selectorInjective
              selectorScratchDisjoint)
            (jointBasisToCore basis) =
          sharedUniformOutsideBasis p selectorWire selectorInjective
            selectorScratchDisjoint background
    · rw [if_pos outsideCore]
      by_cases scratchCore :
          VerifiedCircuitCore.uniformPreparationScratchZero p.selectorWidth
            (VerifiedCircuitCore.restrictToPlacedWires
              (sharedUniformCorePlacement p selectorWire selectorInjective
                selectorScratchDisjoint)
              (jointBasisToCore basis))
      · exfalso
        apply outsideSelector
        exact selectorIff.mpr ⟨outsideIff.mp outsideCore, scratchIff.mp scratchCore⟩
      · rw [if_neg scratchCore]
    · rw [if_neg outsideCore]

/--
従来の Q レイアウト上の一様準備仕様を、共有 core component の `correct` field
だけから得る。命令列の再帰的な振幅証明は Q package 側では使わない。
-/
theorem prepareUniformSelectorOnWiresCircuit_correct_over_sharedCore
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      (selectorSliceWires p selectorWire).Disjoint (uniformScratchWires p))
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorZero : ∀ index, background (selectorWire index) = false)
    (backgroundScratchZero : ∀ wire ∈ uniformScratchWires p,
      background wire = false) :
    applyOperator
        (Circuit.toIdealOperator primitiveGateOperator
          (prepareUniformSelectorOnWiresCircuit p selectorWire))
        (liftSelectorStateOver p selectorWire background
          (zeroSelectorKet p.selectorWidth)) =
      liftSelectorStateOver p selectorWire background
        (idealUniformSelectorState p.selectorWidth p.selectorCount) := by
  let component := frozenUniformPreparationOnJointBasisComponent p selectorWire
    selectorInjective selectorScratchDisjoint background
  have sharedScratchZero : ∀ index,
      background (sharedUniformScratchWire p index) = false := by
    intro index
    exact backgroundScratchZero _
      (sharedUniformScratchWire_mem_uniformScratchWires p index)
  have initialEq : component.initialState = VerifiedCircuitCore.basisKet background :=
    frozenUniformPreparationOnJointBasisComponent_initialState_eq_basisKet
      p selectorWire selectorInjective selectorScratchDisjoint background
      selectorZero sharedScratchZero
  have targetEq : component.targetState =
      liftSelectorStateOver p selectorWire background
        (idealUniformSelectorState p.selectorWidth p.selectorCount) :=
    frozenUniformPreparationOnJointBasisComponent_targetState_eq_liftSelectorStateOver
      p selectorWire selectorInjective selectorScratchDisjoint background
      backgroundScratchZero
  change applyOperator
      (VerifiedCircuitCore.Circuit.denote primitiveGateOperator component.circuit)
      (liftSelectorStateOver p selectorWire background
        (zeroSelectorKet p.selectorWidth)) = _
  rw [liftSelectorStateOver_zeroSelectorKet p selectorWire background selectorZero,
    ← initialEq]
  change VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote primitiveGateOperator component.circuit)
      component.initialState = _
  rw [component.correct, targetEq]

/-- 任意の system 基底に対する column selector 一様準備の共有 core 系。 -/
theorem prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    applyOperator
        (Circuit.toIdealOperator primitiveGateOperator
          (prepareUniformColumnSelectorCircuit p))
        (basisKet (zeroAncillaJointBasis p system)) =
      liftSelectorStateOver p (columnSelectorWire p)
        (zeroAncillaJointBasis p system)
        (idealUniformSelectorState p.selectorWidth p.selectorCount) := by
  change applyOperator
      (Circuit.toIdealOperator primitiveGateOperator
        (prepareUniformColumnSelectorCircuit p))
      (VerifiedCircuitCore.basisKet (zeroAncillaJointBasis p system)) = _
  rw [← liftSelectorStateOver_zeroSelectorKet p (columnSelectorWire p)
    (zeroAncillaJointBasis p system) (by intro index; rfl)]
  exact prepareUniformSelectorOnWiresCircuit_correct_over_sharedCore p
    (columnSelectorWire p) (sharedColumnSelectorWire_injective p)
    (sharedColumnSelector_uniformScratch_disjoint p)
    (zeroAncillaJointBasis p system) (by intro index; rfl) (by
      intro wire member
      rcases List.mem_map.mp member with ⟨index, _, rfl⟩
      rfl)

/-- 任意の system 基底に対する row selector 一様準備の共有 core 系。 -/
theorem prepareUniformRowSelectorCircuit_systemBasis_correct_sharedCore
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    applyOperator
        (Circuit.toIdealOperator primitiveGateOperator
          (prepareUniformRowSelectorCircuit p))
        (basisKet (zeroAncillaJointBasis p system)) =
      liftSelectorStateOver p (rowSelectorWire p)
        (zeroAncillaJointBasis p system)
        (idealUniformSelectorState p.selectorWidth p.selectorCount) := by
  change applyOperator
      (Circuit.toIdealOperator primitiveGateOperator
        (prepareUniformRowSelectorCircuit p))
      (VerifiedCircuitCore.basisKet (zeroAncillaJointBasis p system)) = _
  rw [← liftSelectorStateOver_zeroSelectorKet p (rowSelectorWire p)
    (zeroAncillaJointBasis p system) (by intro index; rfl)]
  exact prepareUniformSelectorOnWiresCircuit_correct_over_sharedCore p
    (rowSelectorWire p) (sharedRowSelectorWire_injective p)
    (sharedRowSelector_uniformScratch_disjoint p)
    (zeroAncillaJointBasis p system) (by intro index; rfl) (by
      intro wire member
      rcases List.mem_map.mp member with ⟨index, _, rfl⟩
      rfl)

end

end ProbabilityGeneratorQProof
