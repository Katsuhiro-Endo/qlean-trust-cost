import QLean.Generator.Analysis.QParameters
import QLean.Circuits.Foundation.UniformPreparationFullOperatorAnalytic
import QLean.Circuits.Foundation.WireEmbeddingAnalytic

/-!
# 共有一様準備作用素のQレイアウト解析target

共有coreの独立full-space作用素を、QのselectorとAND-work prefixへ埋め込み、
所属付き`JointBasis`へ基底付け替えする。このmoduleは回路実装を参照しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Qパラメータを共有一様準備の解析パラメータへ写す。 -/
def sharedUniformPreparationParameters (p : QParameters) :
    VerifiedCircuitCore.UniformPreparationParameters where
  width := p.selectorWidth
  validCount := p.selectorCount
  validCountPositive := p.selectorCount_pos
  validCountLeCapacity := p.selectorCount_le_capacity

/-- 所属付きQ wireを、ancilla先頭の標準数値wireへ写す純粋な符号化。 -/
def analyticWireToCanonicalFin {ancillaQubits systemQubits : Nat} :
    Wire ancillaQubits systemQubits → Fin (ancillaQubits + systemQubits)
  | .ancilla index =>
      ⟨index, Nat.lt_add_right systemQubits index.isLt⟩
  | .system index =>
      ⟨ancillaQubits + index,
        Nat.add_lt_add_left index.isLt ancillaQubits⟩

/-- 標準数値化はwireの所属と添字を保存する。 -/
theorem analyticWireToCanonicalFin_injective
    {ancillaQubits systemQubits : Nat} :
    Function.Injective
      (analyticWireToCanonicalFin
        (ancillaQubits := ancillaQubits)
        (systemQubits := systemQubits)) := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [analyticWireToCanonicalFin, Fin.ext_iff] <;> omega

/-- 標準数値wireを所属付きQ wireへ戻す純粋な復号。 -/
def analyticCanonicalFinToWire {ancillaQubits systemQubits : Nat}
    (index : Fin (ancillaQubits + systemQubits)) :
    Wire ancillaQubits systemQubits :=
  if ancilla : index.val < ancillaQubits then
    .ancilla ⟨index.val, ancilla⟩
  else
    .system ⟨index.val - ancillaQubits, by omega⟩

/-- wire符号化後の復号は恒等である。 -/
@[simp] theorem analyticCanonicalFinToWire_wireToCanonicalFin
    {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits) :
    analyticCanonicalFinToWire (analyticWireToCanonicalFin wire) = wire := by
  cases wire with
  | ancilla index =>
      simp [analyticCanonicalFinToWire, analyticWireToCanonicalFin, index.isLt]
  | system index =>
      simp [analyticCanonicalFinToWire, analyticWireToCanonicalFin]

/-- wire復号後の符号化も恒等である。 -/
@[simp] theorem analyticWireToCanonicalFin_canonicalFinToWire
    {ancillaQubits systemQubits : Nat}
    (index : Fin (ancillaQubits + systemQubits)) :
    analyticWireToCanonicalFin (analyticCanonicalFinToWire index) = index := by
  by_cases ancilla : index.val < ancillaQubits
  · simp [analyticCanonicalFinToWire, ancilla, analyticWireToCanonicalFin]
  · simp [analyticCanonicalFinToWire, ancilla,
      analyticWireToCanonicalFin, Fin.ext_iff]
    omega

/-- 所属付きQ基底と共有core標準基底の純粋な同値。 -/
def analyticJointBasisCoreEquiv (ancillaQubits systemQubits : Nat) :
    JointBasis ancillaQubits systemQubits ≃
      VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits) where
  toFun basis := fun index => basis (analyticCanonicalFinToWire index)
  invFun basis := fun wire => basis (analyticWireToCanonicalFin wire)
  left_inv basis := by
    funext wire
    simp
  right_inv basis := by
    funext index
    simp

/-- 共有core作用素を所属付きQ基底へ戻す純粋な乗法準同型。 -/
def analyticReindexCoreOperatorToJoint
    {ancillaQubits systemQubits : Nat} :
    VerifiedCircuitCore.Operator
        (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits)) →*
      Operator (JointBasis ancillaQubits systemQubits) :=
  (Matrix.reindexRingEquiv ℂ
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm).toMonoidHom

/-- selector幅はQのAND-work幅以下である。 -/
theorem analyticSelectorWidth_le_andWorkWidth (p : QParameters) :
    p.selectorWidth ≤ p.andWorkWidth := by
  simp [QParameters.andWorkWidth]
  omega

/-- 共有compilerの局所scratchをQのAND-work prefixへ置く。 -/
def analyticSharedUniformScratchWire (p : QParameters)
    (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire
    ⟨index.val,
      lt_of_lt_of_le index.isLt (analyticSelectorWidth_le_andWorkWidth p)⟩

/-- Qの一様準備が利用するAND-work wire列。 -/
def analyticUniformPreparationScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.andWorkWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire index

/-- 局所scratchはQのAND-work wire列に属する。 -/
theorem analyticSharedUniformScratchWire_mem (p : QParameters)
    (index : Fin p.selectorWidth) :
    analyticSharedUniformScratchWire p index ∈
      analyticUniformPreparationScratchWires p := by
  unfold analyticSharedUniformScratchWire analyticUniformPreparationScratchWires
  apply List.mem_map.mpr
  exact ⟨⟨index.val,
    lt_of_lt_of_le index.isLt (analyticSelectorWidth_le_andWorkWidth p)⟩,
    List.mem_finRange _, rfl⟩

/-- 局所幅`2w`の前半をselector、後半をscratchへ写す。 -/
def analyticSharedUniformLocalWire (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (index : Fin (2 * p.selectorWidth)) :
    Wire p.ancillaWidth p.systemWidth :=
  if selector : index.val < p.selectorWidth then
    selectorWire ⟨index.val, selector⟩
  else
    analyticSharedUniformScratchWire p
      ⟨index.val - p.selectorWidth, by omega⟩

/-- selectorとscratchが交わらなければ局所配置は単射である。 -/
theorem analyticSharedUniformLocalWire_injective
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (analyticUniformPreparationScratchWires p)) :
    Function.Injective (analyticSharedUniformLocalWire p selectorWire) := by
  intro first second equal
  by_cases firstSelector : first.val < p.selectorWidth
  · by_cases secondSelector : second.val < p.selectorWidth
    · have selectorEqual :
          selectorWire ⟨first.val, firstSelector⟩ =
            selectorWire ⟨second.val, secondSelector⟩ := by
        simpa [analyticSharedUniformLocalWire, firstSelector,
          secondSelector] using equal
      have indexEqual := selectorInjective selectorEqual
      have valueEqual : first.val = second.val :=
        congrArg (fun index : Fin p.selectorWidth => index.val) indexEqual
      exact Fin.ext valueEqual
    · exfalso
      have selectorMember : selectorWire ⟨first.val, firstSelector⟩ ∈
          (List.finRange p.selectorWidth).map selectorWire :=
        List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
      have scratchMember := analyticSharedUniformScratchWire_mem p
        ⟨second.val - p.selectorWidth, by omega⟩
      have crossEqual : selectorWire ⟨first.val, firstSelector⟩ =
          analyticSharedUniformScratchWire p
            ⟨second.val - p.selectorWidth, by omega⟩ := by
        simpa [analyticSharedUniformLocalWire, firstSelector,
          secondSelector] using equal
      exact (List.disjoint_left.mp selectorScratchDisjoint)
        selectorMember (crossEqual.symm ▸ scratchMember)
  · by_cases secondSelector : second.val < p.selectorWidth
    · exfalso
      have selectorMember : selectorWire ⟨second.val, secondSelector⟩ ∈
          (List.finRange p.selectorWidth).map selectorWire :=
        List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
      have scratchMember := analyticSharedUniformScratchWire_mem p
        ⟨first.val - p.selectorWidth, by omega⟩
      have crossEqual : analyticSharedUniformScratchWire p
            ⟨first.val - p.selectorWidth, by omega⟩ =
          selectorWire ⟨second.val, secondSelector⟩ := by
        simpa [analyticSharedUniformLocalWire, firstSelector,
          secondSelector] using equal
      exact (List.disjoint_left.mp selectorScratchDisjoint)
        selectorMember (crossEqual ▸ scratchMember)
    · have scratchEqual : analyticSharedUniformScratchWire p
            ⟨first.val - p.selectorWidth, by omega⟩ =
          analyticSharedUniformScratchWire p
            ⟨second.val - p.selectorWidth, by omega⟩ := by
        simpa [analyticSharedUniformLocalWire, firstSelector,
          secondSelector] using equal
      have valueEqual : first.val - p.selectorWidth =
          second.val - p.selectorWidth := by
        have indexEqual :=
          (QLayout.oracleSlice
            (OracleWorkLayout.canonical p).andWork).index_injective
            (Wire.ancilla.inj scratchEqual)
        exact congrArg Fin.val indexEqual
      apply Fin.ext
      omega

/-- 局所一様準備wireからQ標準数値wireへの解析embedding。 -/
def analyticSharedUniformCorePlacement
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (analyticUniformPreparationScratchWires p)) :
    Fin (2 * p.selectorWidth) ↪ Fin (p.ancillaWidth + p.systemWidth) where
  toFun := analyticWireToCanonicalFin ∘
    analyticSharedUniformLocalWire p selectorWire
  inj' := analyticWireToCanonicalFin_injective.comp
    (analyticSharedUniformLocalWire_injective p selectorWire
      selectorInjective selectorScratchDisjoint)

/-- Restricting a Q basis along the analytic shared-core placement reads the
corresponding Q wire. -/
@[simp] theorem restrictToPlacedWires_analyticSharedUniformCorePlacement
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth →
      Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (analyticUniformPreparationScratchWires p))
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (index : Fin (2 * p.selectorWidth)) :
    VerifiedCircuitCore.restrictToPlacedWires
        (analyticSharedUniformCorePlacement p selectorWire selectorInjective
          selectorScratchDisjoint)
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth basis) index =
      basis (analyticSharedUniformLocalWire p selectorWire index) := by
  simp [VerifiedCircuitCore.restrictToPlacedWires,
    analyticSharedUniformCorePlacement,
    analyticJointBasisCoreEquiv]

/-- The local core scratch half maps exactly to Q's shared AND-work prefix. -/
@[simp] theorem analyticSharedUniformLocalWire_scratch
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth →
      Wire p.ancillaWidth p.systemWidth)
    (index : Fin p.selectorWidth) :
    analyticSharedUniformLocalWire p selectorWire
        (VerifiedCircuitCore.uniformPreparationAnalyticScratchWire
          p.selectorWidth index) =
      analyticSharedUniformScratchWire p index := by
  simp [analyticSharedUniformLocalWire,
    VerifiedCircuitCore.uniformPreparationAnalyticScratchWire]

/-- column selectorの純粋なQ wire割当て。 -/
def sharedUniformAnalyticColumnSelectorWire (p : QParameters)
    (index : Fin p.selectorWidth) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).columnSelector.ancillaWire index

/-- row selectorの純粋なQ wire割当て。 -/
def sharedUniformAnalyticRowSelectorWire (p : QParameters)
    (index : Fin p.selectorWidth) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).rowSelector.ancillaWire index

/-- column selector割当ては単射である。 -/
theorem sharedUniformAnalyticColumnSelectorWire_injective (p : QParameters) :
    Function.Injective (sharedUniformAnalyticColumnSelectorWire p) := by
  intro left right equal
  apply (QLayout.canonical p).columnSelector.index_injective
  exact Wire.ancilla.inj equal

/-- row selector割当ては単射である。 -/
theorem sharedUniformAnalyticRowSelectorWire_injective (p : QParameters) :
    Function.Injective (sharedUniformAnalyticRowSelectorWire p) := by
  intro left right equal
  apply (QLayout.canonical p).rowSelector.index_injective
  exact Wire.ancilla.inj equal

/-- 左slice末尾が右slice先頭以下なら、両者のwire列は交わらない。 -/
theorem analyticRegisterSlice_disjoint_of_end_le_start
    {ancillaWidth systemWidth leftWidth rightWidth : Nat}
    (left : RegisterSlice ancillaWidth leftWidth)
    (right : RegisterSlice ancillaWidth rightWidth)
    (separated : left.start + leftWidth ≤ right.start) :
    ((List.finRange leftWidth).map
        (left.ancillaWire : Fin leftWidth → Wire ancillaWidth systemWidth)).Disjoint
      ((List.finRange rightWidth).map
        (right.ancillaWire : Fin rightWidth → Wire ancillaWidth systemWidth)) := by
  rw [List.disjoint_left]
  intro wire leftMember rightMember
  rcases List.mem_map.mp leftMember with ⟨leftIndex, _, leftEqual⟩
  rcases List.mem_map.mp rightMember with ⟨rightIndex, _, rightEqual⟩
  have indexEqual : left.index leftIndex = right.index rightIndex :=
    Wire.ancilla.inj (leftEqual.trans rightEqual.symm)
  have valueEqual := congrArg Fin.val indexEqual
  simp [RegisterSlice.index] at valueEqual
  omega

/-- column selectorとAND-workは交わらない。 -/
theorem sharedUniformAnalyticColumnSelector_scratch_disjoint (p : QParameters) :
    ((List.finRange p.selectorWidth).map
      (sharedUniformAnalyticColumnSelectorWire p)).Disjoint
        (analyticUniformPreparationScratchWires p) := by
  apply analyticRegisterSlice_disjoint_of_end_le_start
  simp [QLayout.canonical, QLayout.oracleSlice, OracleWorkLayout.canonical,
    RegisterSlice.compose, QParameters.oracleWorkWidth]
  omega

/-- row selectorとAND-workは交わらない。 -/
theorem sharedUniformAnalyticRowSelector_scratch_disjoint (p : QParameters) :
    ((List.finRange p.selectorWidth).map
      (sharedUniformAnalyticRowSelectorWire p)).Disjoint
        (analyticUniformPreparationScratchWires p) := by
  apply analyticRegisterSlice_disjoint_of_end_le_start
  simp [QLayout.canonical, QLayout.oracleSlice, OracleWorkLayout.canonical,
    RegisterSlice.compose, QParameters.oracleWorkWidth]
  omega

/-- 共有core full-space targetをcolumn selector配置へ持ち上げた独立作用素。 -/
def sharedCoreColumnUniformPreparationFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  analyticReindexCoreOperatorToJoint <|
    VerifiedCircuitCore.wireLiftOperator
      (analyticSharedUniformCorePlacement p (sharedUniformAnalyticColumnSelectorWire p)
        (sharedUniformAnalyticColumnSelectorWire_injective p)
        (sharedUniformAnalyticColumnSelector_scratch_disjoint p))
      (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator
        (sharedUniformPreparationParameters p))

/-- 共有core full-space targetをrow selector配置へ持ち上げた独立作用素。 -/
def sharedCoreRowUniformPreparationFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  analyticReindexCoreOperatorToJoint <|
    VerifiedCircuitCore.wireLiftOperator
      (analyticSharedUniformCorePlacement p (sharedUniformAnalyticRowSelectorWire p)
        (sharedUniformAnalyticRowSelectorWire_injective p)
        (sharedUniformAnalyticRowSelector_scratch_disjoint p))
      (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator
        (sharedUniformPreparationParameters p))

end

end ProbabilityGeneratorQProof
