import QLean.Generator.Analysis.QParameters
import QLean.Circuits.Foundation.UniformPreparationAbstract

/-!
# Q selector 一様状態の解析的レイアウト

共有 core の回路非依存な selector 値・理想状態を Q の所属付き wire 配置へ載せる。
この module は実装回路を参照しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 幅 `width` の selector 計算基底。 -/
abbrev AbstractSelectorBasis (width : Nat) :=
  VerifiedCircuitCore.AbstractSelectorBasis width

/-- selector 全零基底。 -/
abbrev zeroSelectorBasis (width : Nat) :=
  VerifiedCircuitCore.zeroSelectorBasis width

/-- selector 全零 ket。 -/
abbrev zeroSelectorKet (width : Nat) :=
  VerifiedCircuitCore.zeroSelectorKet width

/-- selector bit 列の little-endian 自然数値。 -/
abbrev selectorValue (width : Nat) :=
  VerifiedCircuitCore.selectorValue width

/-- selector 値は幅の容量未満である。 -/
theorem selectorValue_lt_capacity
    (width : Nat) (basis : AbstractSelectorBasis width) :
    selectorValue width basis < 2 ^ width :=
  VerifiedCircuitCore.selectorValue_lt_capacity width basis

/-- selector 値の各 bit は元の selector bit と一致する。 -/
theorem selectorValue_testBit
    (width : Nat) (basis : AbstractSelectorBasis width)
    (index : Fin width) :
    (selectorValue width basis).testBit index.val = basis index :=
  VerifiedCircuitCore.selectorValue_testBit width basis index

/-- 有効 selector だけへ振幅 `1/√validCount` を与える理想状態。 -/
abbrev idealUniformSelectorState (width validCount : Nat) :=
  VerifiedCircuitCore.idealUniformSelectorState width validCount

/-- selector の Q wire 列。 -/
def selectorSliceWires
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map selectorWire

/-- Q 計算基底から selector slice を読む。 -/
def projectSelectorBasis
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    AbstractSelectorBasis p.selectorWidth :=
  fun index => basis (selectorWire index)

/-- selector slice 外が全零である条件。 -/
def OutsideSelectorZero
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire, wire ∉ selectorSliceWires p selectorWire → basis wire = false

/-- 全 Q wire が零の計算基底。 -/
def zeroJointBasis (p : QParameters) :
    JointBasis p.ancillaWidth p.systemWidth :=
  fun _ => false

/-- selector 状態を selector 外全零の Q 状態へ持ち上げる。 -/
noncomputable def liftSelectorState
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (state : AbstractSelectorBasis p.selectorWidth → ℂ) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ := by
  classical
  exact fun basis =>
    if OutsideSelectorZero p selectorWire basis then
      state (projectSelectorBasis p selectorWire basis)
    else 0

/-- selector 外と指定背景が一致する条件。 -/
def OutsideSelectorMatches
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire, wire ∉ selectorSliceWires p selectorWire →
    basis wire = background wire

/-- selector 状態を、selector 外を指定背景に固定した Q 状態へ持ち上げる。 -/
noncomputable def liftSelectorStateOver
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (state : AbstractSelectorBasis p.selectorWidth → ℂ) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ := by
  classical
  exact fun basis =>
    if OutsideSelectorMatches p selectorWire background basis then
      state (projectSelectorBasis p selectorWire basis)
    else 0

/-- 背景の selector が全零なら、全零 selector ket の持上げは背景 ket である。 -/
theorem liftSelectorStateOver_zeroSelectorKet
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorZero : ∀ index, background (selectorWire index) = false) :
    liftSelectorStateOver p selectorWire background
        (zeroSelectorKet p.selectorWidth) =
      VerifiedCircuitCore.basisKet background := by
  funext basis
  unfold liftSelectorStateOver
  by_cases basisEqual : basis = background
  · subst basis
    have outside : OutsideSelectorMatches p selectorWire background background := by
      intro wire _
      rfl
    rw [if_pos outside]
    have projected : projectSelectorBasis p selectorWire background =
        zeroSelectorBasis p.selectorWidth := by
      funext index
      exact selectorZero index
    rw [projected]
    simp [VerifiedCircuitCore.zeroSelectorKet, VerifiedCircuitCore.basisKet]
  · have rightZero : VerifiedCircuitCore.basisKet background basis = 0 := by
      simp [VerifiedCircuitCore.basisKet, basisEqual]
    rw [rightZero]
    by_cases outside : OutsideSelectorMatches p selectorWire background basis
    · rw [if_pos outside]
      change VerifiedCircuitCore.zeroSelectorKet p.selectorWidth
        (projectSelectorBasis p selectorWire basis) = 0
      unfold VerifiedCircuitCore.zeroSelectorKet VerifiedCircuitCore.basisKet
      simp only [VerifiedMath.Basis.vector_apply]
      rw [if_neg]
      intro projectedEqual
      apply basisEqual
      funext wire
      by_cases member : wire ∈ selectorSliceWires p selectorWire
      · rcases List.mem_map.mp member with ⟨index, _, wireEqual⟩
        subst wire
        have bitEqual := congrFun projectedEqual index
        calc
          basis (selectorWire index) = false := by
            simpa [projectSelectorBasis, VerifiedCircuitCore.zeroSelectorBasis]
              using bitEqual
          _ = background (selectorWire index) := (selectorZero index).symm
      · exact outside wire member
    · rw [if_neg outside]

end

end ProbabilityGeneratorQProof
