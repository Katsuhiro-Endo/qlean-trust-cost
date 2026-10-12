import QLean.Circuits.Foundation.BoolMultiControlledRotationCorrectness
import QLean.Circuits.Foundation.UniformPreparation
import QLean.Circuits.Foundation.UniformPreparationAbstract

/-!
# 任意サイズ一様状態準備の実回路正しさ

各Bool制御回転命令の疎な行列意味論を、clean scratch上の抽象二分木回転へ接続する。
解析targetは`UniformPreparationAnalytic`で回路から独立に定義されている。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- local selector全wireの自然な列。 -/
def uniformPreparationSelectorWires (width : Nat) : List (Fin (2 * width)) :=
  (List.finRange width).map (uniformPreparationSelectorWire width)

/-- selector wire埋込みは単射である。 -/
theorem uniformPreparationSelectorWire_injective (width : Nat) :
    Function.Injective (uniformPreparationSelectorWire width) := by
  intro first second equal
  apply Fin.ext
  have values := congrArg (fun wire : Fin (2 * width) => wire.val) equal
  simpa [uniformPreparationSelectorWire] using values

/-- scratch wire埋込みは単射である。 -/
theorem uniformPreparationScratchWire_injective (width : Nat) :
    Function.Injective (uniformPreparationScratchWire width) := by
  intro first second equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simpa [uniformPreparationScratchWire] using values

/-- local scratch wire列は重複しない。 -/
theorem uniformPreparationScratchWires_nodup (width : Nat) :
    (uniformPreparationScratchWires width).Nodup := by
  unfold uniformPreparationScratchWires
  exact List.Nodup.map (uniformPreparationScratchWire_injective width)
    (List.nodup_finRange width)

/-- selector wire列とscratch wire列は互いに素である。 -/
theorem uniformPreparationSelectorScratch_disjoint (width : Nat) :
    (uniformPreparationSelectorWires width).Disjoint
      (uniformPreparationScratchWires width) := by
  rw [List.disjoint_left]
  intro selector selectorMember scratchMember
  rcases List.mem_map.mp selectorMember with ⟨selectorIndex, _, rfl⟩
  rcases List.mem_map.mp scratchMember with ⟨scratchIndex, _, scratchEqual⟩
  have values := congrArg Fin.val scratchEqual
  simp [uniformPreparationSelectorWire, uniformPreparationScratchWire] at values
  omega

/-- 命令の制御wire列の長さは解析制御列の長さに等しい。 -/
@[simp] theorem uniformRotationInstructionControls_length
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    (uniformRotationInstructionControls width instruction wellFormed).length =
      instruction.controls.length := by
  simp [uniformRotationInstructionControls]

/-- 単射なselector配置により命令制御wireは重複しない。 -/
theorem uniformRotationInstructionControls_nodup
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    ((uniformRotationInstructionControls width instruction wellFormed).map
      Prod.fst).Nodup := by
  have indexNodup : (instruction.controls.map Prod.fst).Nodup :=
    wellFormed.2.2.2
  rw [show
      (uniformRotationInstructionControls width instruction wellFormed).map
          Prod.fst =
        instruction.controls.attach.map fun control =>
          uniformPreparationSelectorWire width
            ⟨control.1.1, wellFormed.2.1 control.1 control.2⟩ by
    simp [uniformRotationInstructionControls, List.map_map]]
  rw [List.nodup_iff_injective_get]
  intro first second wireEqual
  have firstBound : first.val < (instruction.controls.map Prod.fst).length := by
    simpa using first.isLt
  have secondBound : second.val < (instruction.controls.map Prod.fst).length := by
    simpa using second.isLt
  let firstIndex : Fin (instruction.controls.map Prod.fst).length :=
    ⟨first.val, firstBound⟩
  let secondIndex : Fin (instruction.controls.map Prod.fst).length :=
    ⟨second.val, secondBound⟩
  have selectorEqual :
      (⟨(instruction.controls.map Prod.fst).get firstIndex,
          by
            simpa [firstIndex] using
              wellFormed.2.1
                (instruction.controls.get
                  ⟨first.val, by simpa using first.isLt⟩)
                (instruction.controls.get_mem
                  ⟨first.val, by simpa using first.isLt⟩)⟩ : Fin width) =
      (⟨(instruction.controls.map Prod.fst).get secondIndex,
          by
            simpa [secondIndex] using
              wellFormed.2.1
                (instruction.controls.get
                  ⟨second.val, by simpa using second.isLt⟩)
                (instruction.controls.get_mem
                  ⟨second.val, by simpa using second.isLt⟩)⟩ : Fin width) := by
    apply uniformPreparationSelectorWire_injective width
    simpa [firstIndex, secondIndex, uniformRotationInstructionControls] using
      wireEqual
  have valueEqual :
      (instruction.controls.map Prod.fst).get firstIndex =
        (instruction.controls.map Prod.fst).get secondIndex := by
    exact congrArg Fin.val selectorEqual
  have positionEqual := (List.nodup_iff_injective_get.mp indexNodup) valueEqual
  apply Fin.ext
  have positionValues := congrArg
    (fun index : Fin (instruction.controls.map Prod.fst).length => index.val)
    positionEqual
  simpa [firstIndex, secondIndex] using positionValues

/-- well-formed命令のtargetは制御wire列に含まれない。 -/
theorem uniformRotationInstructionTarget_not_mem
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    uniformRotationInstructionTarget width instruction wellFormed ∉
      (uniformRotationInstructionControls width instruction wellFormed).map
        Prod.fst := by
  intro member
  rw [show
      (uniformRotationInstructionControls width instruction wellFormed).map
          Prod.fst =
        instruction.controls.attach.map fun control =>
          uniformPreparationSelectorWire width
            ⟨control.1.1, wellFormed.2.1 control.1 control.2⟩ by
    simp [uniformRotationInstructionControls, List.map_map]] at member
  rcases List.mem_map.mp member with ⟨control, controlMember, wireEqual⟩
  have indexEqual := uniformPreparationSelectorWire_injective width wireEqual.symm
  apply wellFormed.2.2.1
  rw [List.mem_map]
  refine ⟨control.1, control.2, ?_⟩
  exact (congrArg Fin.val indexEqual).symm

/-- 各命令の制御wireはselector sliceに属する。 -/
theorem uniformRotationInstructionControls_mem_selector
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    ∀ wire ∈ (uniformRotationInstructionControls width instruction wellFormed).map
        Prod.fst,
      wire ∈ uniformPreparationSelectorWires width := by
  intro wire member
  rw [show
      (uniformRotationInstructionControls width instruction wellFormed).map
          Prod.fst =
        instruction.controls.attach.map fun control =>
          uniformPreparationSelectorWire width
            ⟨control.1.1, wellFormed.2.1 control.1 control.2⟩ by
    simp [uniformRotationInstructionControls, List.map_map]] at member
  rcases List.mem_map.mp member with ⟨source, _, rfl⟩
  exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩

/-- 各命令のtarget wireはselector sliceに属する。 -/
theorem uniformRotationInstructionTarget_mem_selector
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    uniformRotationInstructionTarget width instruction wellFormed ∈
      uniformPreparationSelectorWires width :=
  List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩

/-- 一命令compilerの制御・scratch・target配置は重複しない。 -/
theorem uniformRotationInstruction_layoutNodup
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    ((uniformRotationInstructionControls width instruction wellFormed).map
        Prod.fst ++ uniformPreparationScratchWires width ++
      [uniformRotationInstructionTarget width instruction wellFormed]).Nodup := by
  let controls :=
    (uniformRotationInstructionControls width instruction wellFormed).map Prod.fst
  let scratches := uniformPreparationScratchWires width
  let target := uniformRotationInstructionTarget width instruction wellFormed
  have controlsNodup : controls.Nodup :=
    uniformRotationInstructionControls_nodup width instruction wellFormed
  have scratchesNodup : scratches.Nodup :=
    uniformPreparationScratchWires_nodup width
  have targetOutsideControls : target ∉ controls :=
    uniformRotationInstructionTarget_not_mem width instruction wellFormed
  have controlsScratchDisjoint : controls.Disjoint scratches := by
    rw [List.disjoint_left]
    intro wire controlMember scratchMember
    exact (List.disjoint_left.mp
      (uniformPreparationSelectorScratch_disjoint width))
      (uniformRotationInstructionControls_mem_selector width instruction
        wellFormed wire controlMember) scratchMember
  have targetOutsideScratch : target ∉ scratches := by
    intro scratchMember
    exact (List.disjoint_left.mp
      (uniformPreparationSelectorScratch_disjoint width))
      (uniformRotationInstructionTarget_mem_selector width instruction wellFormed)
      scratchMember
  apply List.nodup_append.mpr
  refine ⟨?_, by simp, ?_⟩
  · exact List.nodup_append.mpr
      ⟨controlsNodup, scratchesNodup, by
        intro left leftMember right rightMember equal
        subst right
        exact (List.disjoint_left.mp controlsScratchDisjoint)
          leftMember rightMember⟩
  · intro wire member finalTarget finalMember equal
    have finalEqual : finalTarget = target := by simpa using finalMember
    subst finalTarget
    subst wire
    rcases List.mem_append.mp member with controlMember | scratchMember
    · exact targetOutsideControls controlMember
    · exact targetOutsideScratch scratchMember

/-- 一命令には幅個のscratchが常に十分である。 -/
theorem uniformRotationInstruction_enoughScratch
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    (uniformRotationInstructionControls width instruction wellFormed).length ≤
      (uniformPreparationScratchWires width).length + 1 := by
  rw [uniformRotationInstructionControls_length]
  simp only [uniformPreparationScratchWires, List.length_map,
    List.length_finRange]
  have allControlsInRange :
      (instruction.controls.map Prod.fst).toFinset ⊆ Finset.range width := by
    intro index member
    rw [List.mem_toFinset] at member
    rcases List.mem_map.mp member with ⟨control, controlMember, rfl⟩
    exact Finset.mem_range.mpr (wellFormed.2.1 control controlMember)
  have cardBound := Finset.card_le_card allControlsInRange
  have lengthBound : instruction.controls.length ≤ width := by
    simpa [List.toFinset_card_of_nodup wellFormed.2.2.2] using cardBound
  omega

/-- 一命令の基本ゲート回路はclean scratch入力上で独立疎行列に一致する。 -/
theorem compileUniformRotationInstruction_apply_sparse
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width)
    (output input : QubitBasis (2 * width))
    (scratchZero : ∀ wire ∈ uniformPreparationScratchWires width,
      input wire = false) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (compileUniformRotationInstruction width instruction wellFormed)
        output input =
      boolControlledRyAmplitude
        (uniformRotationInstructionControls width instruction wellFormed)
        (uniformRotationInstructionTarget width instruction wellFormed)
        instruction.angle.uniformValue output input := by
  apply boolMultiControlledRy_apply_sparse
  · exact uniformRotationInstruction_enoughScratch width instruction wellFormed
  · exact uniformRotationInstruction_layoutNodup width instruction wellFormed
  · exact scratchZero

/-- 指定wireだけを指定Bool値で置換する直接基底変換。 -/
def replaceQubitWire {qubits : Nat} (basis : QubitBasis qubits)
    (target : Fin qubits) (value : Bool) : QubitBasis qubits :=
  fun wire => if wire = target then value else basis wire

/-- 置換後のtarget bitは指定値である。 -/
@[simp] theorem replaceQubitWire_target {qubits : Nat}
    (basis : QubitBasis qubits) (target : Fin qubits) (value : Bool) :
    replaceQubitWire basis target value target = value := by
  simp [replaceQubitWire]

/-- target外のbitは置換で保存される。 -/
theorem replaceQubitWire_outside {qubits : Nat}
    (basis : QubitBasis qubits) (target wire : Fin qubits) (value : Bool)
    (different : wire ≠ target) :
    replaceQubitWire basis target value wire = basis wire := by
  simp [replaceQubitWire, different]

/-- 自身のtarget bit値で置換した基底は元の基底である。 -/
@[simp] theorem replaceQubitWire_self {qubits : Nat}
    (basis : QubitBasis qubits) (target : Fin qubits) :
    replaceQubitWire basis target (basis target) = basis := by
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [replaceQubitWire]
  · simp [replaceQubitWire, equal]

/-- 一wire分解の逆写像は直接置換と一致する。 -/
theorem replaceQubitWire_eq_splitWireEquiv_symm {qubits : Nat}
    (basis : QubitBasis qubits) (target : Fin qubits) (value : Bool) :
    replaceQubitWire basis target value =
      (splitWireEquiv target).symm (value, (splitWireEquiv target basis).2) := by
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [replaceQubitWire, splitWireEquiv]
  · simp [replaceQubitWire, splitWireEquiv, equal]

/-- Bool制御Ryの独立な疎行列作用素。 -/
def boolControlledRyOperator {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (angle : ℝ) : Operator (QubitBasis qubits) :=
  fun output input =>
    boolControlledRyAmplitude controls target angle output input

/-- targetが制御列外ならtarget置換はBool制御条件を変えない。 -/
theorem boolControlsSatisfied_replaceQubitWire {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (targetOutside : target ∉ controls.map Prod.fst)
    (basis : QubitBasis qubits) (value : Bool) :
    boolControlsSatisfied controls (replaceQubitWire basis target value) =
      boolControlsSatisfied controls basis := by
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨wire, expected⟩
      have different : wire ≠ target := by
        intro equal
        apply targetOutside
        simp [equal]
      have tailOutside : target ∉ controls.map Prod.fst := by
        intro member
        apply targetOutside
        simp [member]
      change
        (decide (replaceQubitWire basis target value wire = expected) &&
            boolControlsSatisfied controls (replaceQubitWire basis target value)) =
          (decide (basis wire = expected) && boolControlsSatisfied controls basis)
      rw [replaceQubitWire_outside _ _ _ _ different]
      rw [inductionHypothesis tailOutside]

/-- target以外が等しい条件は一wire分解の逆写像で成立する。 -/
theorem agreesExcept_splitWireEquiv_symm {qubits : Nat}
    (target : Fin qubits) (output : QubitBasis qubits) (value : Bool) :
    agreesExcept target output
      ((splitWireEquiv target).symm
        (value, (splitWireEquiv target output).2)) := by
  intro wire different
  simp [splitWireEquiv, different]

/-- 一wire分解の逆写像がtarget外でoutputと一致する条件は外側成分の一致である。 -/
theorem agreesExcept_splitWireEquiv_symm_iff {qubits : Nat}
    (target : Fin qubits) (output : QubitBasis qubits) (value : Bool)
    (outside : {wire : Fin qubits // wire ≠ target} → Bool) :
    agreesExcept target output
        ((splitWireEquiv target).symm (value, outside)) ↔
      outside = (splitWireEquiv target output).2 := by
  constructor
  · intro agreement
    funext wire
    have valueEqual := agreement wire.1 wire.2
    simpa [splitWireEquiv, wire.2] using valueEqual.symm
  · intro outsideEqual
    subst outside
    exact agreesExcept_splitWireEquiv_symm target output value

/-- 一wire分解の逆写像におけるtarget値は第一成分である。 -/
@[simp] theorem splitWireEquiv_symm_target {qubits : Nat}
    (target : Fin qubits) (outside : {wire : Fin qubits // wire ≠ target} → Bool)
    (value : Bool) :
    (splitWireEquiv target).symm (value, outside) target = value := by
  simp [splitWireEquiv]

/-- 一wire分解の逆写像に対するBool制御条件は外側基底と同じである。 -/
theorem boolControlsSatisfied_splitWireEquiv_symm {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (targetOutside : target ∉ controls.map Prod.fst)
    (output : QubitBasis qubits) (value : Bool) :
    boolControlsSatisfied controls
        ((splitWireEquiv target).symm
          (value, (splitWireEquiv target output).2)) =
      boolControlsSatisfied controls output := by
  rw [← replaceQubitWire_eq_splitWireEquiv_symm]
  exact boolControlsSatisfied_replaceQubitWire controls target targetOutside
    output value

/-- Bool制御Ryの状態作用はtarget bit二値だけの和へ縮約する。 -/
theorem applyOperator_boolControlledRyOperator {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (targetOutside : target ∉ controls.map Prod.fst) (angle : ℝ)
    (state : State (QubitBasis qubits)) (output : QubitBasis qubits) :
    applyOperator (boolControlledRyOperator controls target angle) state output =
      if boolControlsSatisfied controls output then
        ∑ inputBit : Bool,
          localRy angle (output target) inputBit *
            state (replaceQubitWire output target inputBit)
      else state output := by
  unfold applyOperator Matrix.mulVec dotProduct boolControlledRyOperator
  change (∑ input,
      boolControlledRyAmplitude controls target angle output input * state input) = _
  rw [show (∑ input,
      boolControlledRyAmplitude controls target angle output input * state input) =
        ∑ pair : Bool × ({wire : Fin qubits // wire ≠ target} → Bool),
          boolControlledRyAmplitude controls target angle output
              ((splitWireEquiv target).symm pair) *
            state ((splitWireEquiv target).symm pair) by
    exact ((splitWireEquiv target).symm.sum_comp fun input =>
      boolControlledRyAmplitude controls target angle output input *
        state input).symm]
  simp_rw [Fintype.sum_prod_type]
  simp [boolControlledRyAmplitude, agreesExcept_splitWireEquiv_symm_iff,
    splitWireEquiv_symm_target, ← replaceQubitWire_eq_splitWireEquiv_symm]
  rw [boolControlsSatisfied_replaceQubitWire controls target targetOutside
      output true,
    boolControlsSatisfied_replaceQubitWire controls target targetOutside
      output false]
  by_cases enabled : boolControlsSatisfied controls output = true
  · simp [enabled]
  · cases targetValue : output target
    · simp [enabled]
      simpa [targetValue] using
        congrArg state (replaceQubitWire_self output target)
    · simp [enabled]
      simpa [targetValue] using
        congrArg state (replaceQubitWire_self output target)

/-- 状態がuniform scratch全零基底だけに台を持つこと。 -/
def SupportedOnUniformScratchZero (width : Nat)
    (state : State (QubitBasis (2 * width))) : Prop :=
  ∀ basis, (∃ wire ∈ uniformPreparationScratchWires width,
    basis wire = true) → state basis = 0

/-- scratch全零でなければ値1のscratch wireが存在する。 -/
theorem exists_true_of_not_uniformScratchZero (width : Nat)
    (basis : QubitBasis (2 * width))
    (notZero : ¬∀ wire ∈ uniformPreparationScratchWires width,
      basis wire = false) :
    ∃ wire ∈ uniformPreparationScratchWires width, basis wire = true := by
  push Not at notZero
  rcases notZero with ⟨wire, member, value⟩
  refine ⟨wire, member, ?_⟩
  cases bit : basis wire with
  | false => exact (value bit).elim
  | true => rfl

/-- clean scratchに台を持つ状態上で一命令回路と独立疎作用素は一致する。 -/
theorem applyOperator_compileUniformRotationInstruction_eq_ideal
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width)
    (state : State (QubitBasis (2 * width)))
    (support : SupportedOnUniformScratchZero width state) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (compileUniformRotationInstruction width instruction wellFormed)) state =
      applyOperator
        (boolControlledRyOperator
          (uniformRotationInstructionControls width instruction wellFormed)
          (uniformRotationInstructionTarget width instruction wellFormed)
          instruction.angle.uniformValue) state := by
  funext output
  unfold applyOperator Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro input _
  by_cases scratchZero : ∀ wire ∈ uniformPreparationScratchWires width,
      input wire = false
  · change
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (compileUniformRotationInstruction width instruction wellFormed)
          output input * state input =
        boolControlledRyAmplitude
          (uniformRotationInstructionControls width instruction wellFormed)
          (uniformRotationInstructionTarget width instruction wellFormed)
          instruction.angle.uniformValue output input * state input
    rw [compileUniformRotationInstruction_apply_sparse width instruction
      wellFormed output input scratchZero]
  · have dirty := exists_true_of_not_uniformScratchZero width input scratchZero
    rw [support input dirty]
    simp

/-- clean scratch状態への一命令作用はtarget bit二値の和へ縮約する。 -/
theorem applyOperator_compileUniformRotationInstruction
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width)
    (state : State (QubitBasis (2 * width)))
    (support : SupportedOnUniformScratchZero width state)
    (output : QubitBasis (2 * width)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (compileUniformRotationInstruction width instruction wellFormed))
        state output =
      if boolControlsSatisfied
          (uniformRotationInstructionControls width instruction wellFormed)
          output then
        ∑ inputBit : Bool,
          localRy instruction.angle.uniformValue
              (output
                (uniformRotationInstructionTarget width instruction wellFormed))
              inputBit *
            state (replaceQubitWire output
              (uniformRotationInstructionTarget width instruction wellFormed)
              inputBit)
      else state output := by
  rw [applyOperator_compileUniformRotationInstruction_eq_ideal width instruction
    wellFormed state support]
  exact applyOperator_boolControlledRyOperator _ _
    (uniformRotationInstructionTarget_not_mem width instruction wellFormed)
    _ _ _

/-- 一様準備命令はclean scratch台を保存する。 -/
theorem compileUniformRotationInstruction_preserves_support
    (width : Nat) (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width)
    (state : State (QubitBasis (2 * width)))
    (support : SupportedOnUniformScratchZero width state) :
    SupportedOnUniformScratchZero width
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (compileUniformRotationInstruction width instruction wellFormed))
        state) := by
  intro output dirty
  rw [applyOperator_compileUniformRotationInstruction width instruction
    wellFormed state support output]
  have targetOutsideScratch :
      uniformRotationInstructionTarget width instruction wellFormed ∉
        uniformPreparationScratchWires width := by
    intro member
    exact (List.disjoint_left.mp
      (uniformPreparationSelectorScratch_disjoint width))
      (uniformRotationInstructionTarget_mem_selector width instruction wellFormed)
      member
  have dirtyAfterReplace : ∀ value : Bool,
      ∃ wire ∈ uniformPreparationScratchWires width,
        replaceQubitWire output
          (uniformRotationInstructionTarget width instruction wellFormed)
          value wire = true := by
    intro value
    rcases dirty with ⟨wire, member, wireTrue⟩
    refine ⟨wire, member, ?_⟩
    rw [replaceQubitWire_outside]
    · exact wireTrue
    · intro equal
      subst wire
      exact targetOutsideScratch member
  by_cases enabled : boolControlsSatisfied
      (uniformRotationInstructionControls width instruction wellFormed) output
  · simp only [enabled, if_true]
    apply Finset.sum_eq_zero
    intro value _
    rw [support _ (dirtyAfterReplace value)]
    simp
  · simp [enabled, support output dirty]

/-- A source-order list of compiled uniform-rotation instructions preserves
the coherent sector in which every compiler scratch wire is zero.  This is
the list-level invariant needed both by forward uniform preparation and, via
finite-dimensional unitarity, by its inverse. -/
theorem compiledUniformInstructions_preserves_support
    {width : Nat}
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : State (QubitBasis (2 * width)))
    (support : SupportedOnUniformScratchZero width state) :
    SupportedOnUniformScratchZero width
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map fun instruction =>
            compileUniformRotationInstruction width instruction.1
              instruction.2)))
        state) := by
  induction instructions generalizing state with
  | nil =>
      simpa [Circuit.sequence, Circuit.denote, applyOperator] using support
  | cons instruction instructions inductionHypothesis =>
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      exact inductionHypothesis _
        (compileUniformRotationInstruction_preserves_support width
          instruction.1 instruction.2 state support)

/-- The complete arbitrary-width uniform-preparation circuit preserves its
scratch-zero sector for every input state supported there. -/
theorem uniformPreparationCircuit_preserves_support
    (parameters : UniformPreparationParameters)
    (state : State (QubitBasis (2 * parameters.width)))
    (support : SupportedOnUniformScratchZero parameters.width state) :
    SupportedOnUniformScratchZero parameters.width
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (uniformPreparationCircuit parameters)) state) := by
  unfold uniformPreparationCircuit
  exact compiledUniformInstructions_preserves_support
    (attachedUniformRotationPlan parameters.width parameters.validCount
      parameters.validCountLeCapacity) state support

/-- selector状態を同幅scratch全零の全基底状態へ埋め込む。 -/
def liftUniformSelectorState (width : Nat)
    (state : State (AbstractSelectorBasis width)) :
    State (QubitBasis (2 * width)) := by
  classical
  exact fun basis =>
    if uniformPreparationScratchZero width basis then
      state (uniformPreparationSelectorBasis width basis)
    else 0

/-- listによるscratch全零条件と解析仕様の全零条件は同値である。 -/
theorem uniformPreparationScratchZero_iff (width : Nat)
    (basis : QubitBasis (2 * width)) :
    uniformPreparationScratchZero width basis ↔
      ∀ wire ∈ uniformPreparationScratchWires width, basis wire = false := by
  constructor
  · intro scratchZero wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact scratchZero index
  · intro scratchZero index
    exact scratchZero (uniformPreparationScratchWire width index)
      (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)

/-- selector状態のscratch全零埋込みはclean scratch基底だけに台を持つ。 -/
theorem liftUniformSelectorState_supported (width : Nat)
    (state : State (AbstractSelectorBasis width)) :
    SupportedOnUniformScratchZero width
      (liftUniformSelectorState width state) := by
  intro basis dirty
  unfold liftUniformSelectorState
  rw [if_neg]
  intro scratchZero
  rcases dirty with ⟨wire, member, wireTrue⟩
  have allZero := (uniformPreparationScratchZero_iff width basis).mp scratchZero
  rw [allZero wire member] at wireTrue
  contradiction

/-- selector target置換はselector射影上の抽象bit置換へ一致する。 -/
theorem uniformPreparationSelectorBasis_replaceQubitWire
    (width : Nat) (basis : QubitBasis (2 * width))
    (target : Fin width) (value : Bool) :
    uniformPreparationSelectorBasis width
        (replaceQubitWire basis (uniformPreparationSelectorWire width target) value) =
      replaceSelectorBit (uniformPreparationSelectorBasis width basis) target value := by
  funext index
  by_cases equal : index = target
  · subst index
    simp [uniformPreparationSelectorBasis, replaceSelectorBit,
      replaceQubitWire, uniformPreparationSelectorWire]
  · have valueDifferent : index.val ≠ target.val :=
      fun valueEqual => equal (Fin.ext valueEqual)
    simp [uniformPreparationSelectorBasis, replaceSelectorBit,
      replaceQubitWire, uniformPreparationSelectorWire, valueDifferent, equal]

/-- selector targetの置換はscratch全零条件を変えない。 -/
theorem uniformPreparationScratchZero_replaceQubitWire_iff
    (width : Nat) (basis : QubitBasis (2 * width))
    (target : Fin width) (value : Bool) :
    uniformPreparationScratchZero width
        (replaceQubitWire basis (uniformPreparationSelectorWire width target) value) ↔
      uniformPreparationScratchZero width basis := by
  rw [uniformPreparationScratchZero_iff,
    uniformPreparationScratchZero_iff]
  constructor <;> intro scratchZero wire member
  · have targetOutside : wire ≠ uniformPreparationSelectorWire width target := by
      intro equal
      subst wire
      exact (List.disjoint_left.mp
        (uniformPreparationSelectorScratch_disjoint width))
        (List.mem_map.mpr ⟨target, List.mem_finRange _, rfl⟩) member
    simpa [replaceQubitWire_outside _ _ _ _ targetOutside] using
      scratchZero wire member
  · have targetOutside : wire ≠ uniformPreparationSelectorWire width target := by
      intro equal
      subst wire
      exact (List.disjoint_left.mp
        (uniformPreparationSelectorScratch_disjoint width))
        (List.mem_map.mpr ⟨target, List.mem_finRange _, rfl⟩) member
    rw [replaceQubitWire_outside _ _ _ _ targetOutside]
    exact scratchZero wire member

/-- 物理Bool制御条件はselector射影上の抽象制御条件と一致する。 -/
theorem boolControlsSatisfied_uniformRotationInstruction_eq_abstract
    (width : Nat)
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (basis : QubitBasis (2 * width)) :
    boolControlsSatisfied
        (uniformRotationInstructionControls width instruction.1 instruction.2)
        basis =
      abstractControlsSatisfied instruction
        (uniformPreparationSelectorBasis width basis) := by
  unfold boolControlsSatisfied uniformRotationInstructionControls
    abstractControlsSatisfied uniformPreparationSelectorBasis
  rw [List.all_map]
  rfl

/-- selectorValueは標準little-endian計算基底添字に一致する。 -/
theorem selectorValue_eq_qubitBasisLittleEndianIndex
    (width : Nat) (basis : AbstractSelectorBasis width) :
    selectorValue width basis = qubitBasisLittleEndianIndex width basis := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases inWidth : bit < width
  · let wire : Fin width := ⟨bit, inWidth⟩
    rw [show bit = wire.val by rfl,
      selectorValue_testBit width basis wire]
    have recovered := congrFun (qubitBasisOfLittleEndianIndex_index basis) wire
    simpa [qubitBasisOfLittleEndianIndex, wire] using recovered.symm
  · have widthLe : width ≤ bit := Nat.le_of_not_gt inWidth
    have selectorBoundAtBit : selectorValue width basis < 2 ^ bit :=
      lt_of_lt_of_le (selectorValue_lt_capacity width basis)
        (Nat.pow_le_pow_right (by decide) widthLe)
    have qubitBoundAtBit : qubitBasisLittleEndianIndex width basis < 2 ^ bit :=
      lt_of_lt_of_le (qubitBasisLittleEndianIndex_lt basis)
        (Nat.pow_le_pow_right (by decide) widthLe)
    rw [Nat.testBit_eq_false_of_lt selectorBoundAtBit,
      Nat.testBit_eq_false_of_lt qubitBoundAtBit]

/-- 抽象一様selector targetは標準little-endian target stateに一致する。 -/
theorem idealUniformSelectorState_eq_uniformPreparationTargetState
    (parameters : UniformPreparationParameters) :
    idealUniformSelectorState parameters.width parameters.validCount =
      uniformPreparationTargetState parameters := by
  funext basis
  unfold idealUniformSelectorState uniformPreparationTargetState
  rw [selectorValue_eq_qubitBasisLittleEndianIndex]

/-- 一個の実命令回路は抽象一命令作用とscratch全零埋込みを可換にする。 -/
theorem applyOperator_compileUniformRotationInstruction_lift
    (width : Nat)
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : State (AbstractSelectorBasis width)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (compileUniformRotationInstruction width instruction.1 instruction.2))
        (liftUniformSelectorState width state) =
      liftUniformSelectorState width
        (applyAbstractUniformInstruction instruction state) := by
  funext output
  rw [applyOperator_compileUniformRotationInstruction width instruction.1
    instruction.2 (liftUniformSelectorState width state)
    (liftUniformSelectorState_supported width state) output]
  unfold liftUniformSelectorState applyAbstractUniformInstruction
  rw [boolControlsSatisfied_uniformRotationInstruction_eq_abstract]
  let targetIndex : Fin width :=
    ⟨instruction.1.target, instruction.2.1⟩
  have targetWire :
      uniformRotationInstructionTarget width instruction.1 instruction.2 =
        uniformPreparationSelectorWire width targetIndex := rfl
  rw [targetWire]
  by_cases outputClean : uniformPreparationScratchZero width output
  · simp only [outputClean, if_true]
    by_cases enabled : abstractControlsSatisfied instruction
        (uniformPreparationSelectorBasis width output)
    · simp only [enabled, if_true]
      apply Finset.sum_congr rfl
      intro inputBit _
      have afterClean : uniformPreparationScratchZero width
          (replaceQubitWire output
            (uniformPreparationSelectorWire width targetIndex) inputBit) :=
        (uniformPreparationScratchZero_replaceQubitWire_iff width output
          targetIndex inputBit).2 outputClean
      rw [if_pos afterClean]
      rw [uniformPreparationSelectorBasis_replaceQubitWire]
      simp [targetIndex, uniformPreparationSelectorBasis,
        uniformPreparationSelectorWire]
    · have controlsFalse :
          abstractControlsSatisfied instruction
              (uniformPreparationSelectorBasis width output) = false := by
        cases value : abstractControlsSatisfied instruction
            (uniformPreparationSelectorBasis width output)
        · rfl
        · exact (enabled value).elim
      rw [controlsFalse]
      simp
  · simp only [outputClean, if_false]
    by_cases enabled : abstractControlsSatisfied instruction
        (uniformPreparationSelectorBasis width output)
    · simp only [enabled, if_true]
      apply Finset.sum_eq_zero
      intro inputBit _
      have afterDirty : ¬uniformPreparationScratchZero width
          (replaceQubitWire output
            (uniformPreparationSelectorWire width targetIndex) inputBit) :=
        fun afterClean => outputClean
          ((uniformPreparationScratchZero_replaceQubitWire_iff width output
            targetIndex inputBit).1 afterClean)
      rw [if_neg afterDirty]
      simp
    · have controlsFalse :
          abstractControlsSatisfied instruction
              (uniformPreparationSelectorBasis width output) = false := by
        cases value : abstractControlsSatisfied instruction
            (uniformPreparationSelectorBasis width output)
        · rfl
        · exact (enabled value).elim
      rw [controlsFalse]
      simp

/-- 証明付き命令列の実回路も抽象fold作用とscratch全零埋込みを可換にする。 -/
theorem applyOperator_compiledUniformInstructions_lift
    {width : Nat}
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : State (AbstractSelectorBasis width)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map fun instruction =>
            compileUniformRotationInstruction width instruction.1 instruction.2)))
        (liftUniformSelectorState width state) =
      liftUniformSelectorState width
        (runAbstractUniformInstructions instructions state) := by
  induction instructions generalizing state with
  | nil =>
      change Matrix.mulVec
        (1 : Operator (QubitBasis (2 * width)))
        (liftUniformSelectorState width state) = _
      exact Matrix.one_mulVec _
  | cons instruction instructions inductionHypothesis =>
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        runAbstractUniformInstructions, List.foldl_cons, applyOperator_mul]
      rw [applyOperator_compileUniformRotationInstruction_lift width
        instruction state]
      exact inductionHypothesis _

/-- 一様準備正本回路は抽象一様selector targetを厳密に準備する。 -/
theorem uniformPreparationCircuit_correct_lift
    (parameters : UniformPreparationParameters) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (uniformPreparationCircuit parameters))
        (liftUniformSelectorState parameters.width
          (zeroSelectorKet parameters.width)) =
      liftUniformSelectorState parameters.width
        (idealUniformSelectorState parameters.width parameters.validCount) := by
  unfold uniformPreparationCircuit
  rw [applyOperator_compiledUniformInstructions_lift]
  change liftUniformSelectorState parameters.width
      (abstractUniformPreparedState parameters.width parameters.validCount
        parameters.validCountLeCapacity) = _
  rw [abstractUniformPreparedState_correct parameters.width parameters.validCount
    parameters.validCountLeCapacity parameters.validCountPositive]

/-- local一様準備全幅の全零計算基底。 -/
def zeroUniformPreparationBasis (width : Nat) : QubitBasis (2 * width) :=
  fun _ => false

/-- 抽象全零selector ketのscratch全零埋込みは全幅全零ketである。 -/
theorem lift_zeroSelectorKet_eq_zeroUniformPreparationKet (width : Nat) :
    liftUniformSelectorState width (zeroSelectorKet width) =
      basisKet (zeroUniformPreparationBasis width) := by
  funext basis
  by_cases basisEqual : basis = zeroUniformPreparationBasis width
  · subst basis
    have scratchZero : uniformPreparationScratchZero width
        (zeroUniformPreparationBasis width) := by
      intro wire
      rfl
    rw [show liftUniformSelectorState width (zeroSelectorKet width)
        (zeroUniformPreparationBasis width) =
          zeroSelectorKet width
            (uniformPreparationSelectorBasis width
              (zeroUniformPreparationBasis width)) by
      simp [liftUniformSelectorState, scratchZero]]
    have selectorZero :
        uniformPreparationSelectorBasis width
            (zeroUniformPreparationBasis width) =
          zeroSelectorBasis width := by
      rfl
    rw [selectorZero]
    simp [zeroSelectorKet, basisKet]
  · have rightZero : basisKet (zeroUniformPreparationBasis width) basis = 0 := by
      simp [basisKet, basisEqual]
    rw [rightZero]
    unfold liftUniformSelectorState
    by_cases scratchZero : uniformPreparationScratchZero width basis
    · rw [if_pos scratchZero]
      unfold zeroSelectorKet basisKet
      rw [VerifiedMath.Basis.vector_apply]
      rw [if_neg]
      intro selectorEqual
      apply basisEqual
      funext wire
      by_cases selectorWire : wire.val < width
      · let index : Fin width := ⟨wire.val, selectorWire⟩
        have bitEqual := congrFun selectorEqual index
        simpa [uniformPreparationSelectorBasis, zeroSelectorBasis,
          zeroUniformPreparationBasis, index] using bitEqual
      · have widthLe : width ≤ wire.val := Nat.le_of_not_gt selectorWire
        have scratchBound : wire.val - width < width := by
          have wireBound := wire.isLt
          omega
        let index : Fin width := ⟨wire.val - width, scratchBound⟩
        have scratchBit := scratchZero index
        change basis wire = false
        have wireEqual :
            wire = uniformPreparationScratchWire width index := by
          apply Fin.ext
          simp [index, uniformPreparationScratchWire]
          omega
        rw [wireEqual]
        exact scratchBit
    · rw [if_neg scratchZero]

/-- 抽象selector targetのscratch全零埋込みは独立full target stateである。 -/
theorem lift_uniformPreparationTargetState_eq_fullTarget
    (parameters : UniformPreparationParameters) :
    liftUniformSelectorState parameters.width
        (uniformPreparationTargetState parameters) =
      uniformPreparationFullTargetState parameters := by
  rfl

/-- 任意`0<N≤2^w`の共有一様状態準備component。 -/
def uniformPreparationStatePreparationComponent
    (parameters : UniformPreparationParameters) :
    StatePreparationComponent
      (Gate := PrimitiveGate (2 * parameters.width))
      (basis := QubitBasis (2 * parameters.width))
      (primitiveGateOperatorWithSymbols (qubits := 2 * parameters.width) (fun _ => 0)) where
  circuit := uniformPreparationCircuit parameters
  initialState := basisKet (zeroUniformPreparationBasis parameters.width)
  targetState := uniformPreparationFullTargetState parameters
  correct := by
    rw [← lift_zeroSelectorKet_eq_zeroUniformPreparationKet]
    rw [uniformPreparationCircuit_correct_lift]
    rw [idealUniformSelectorState_eq_uniformPreparationTargetState]
    exact lift_uniformPreparationTargetState_eq_fullTarget parameters

end

end VerifiedCircuitCore
