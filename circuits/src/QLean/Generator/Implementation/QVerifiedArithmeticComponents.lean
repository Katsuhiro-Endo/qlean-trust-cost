import QLean.Generator.Implementation.ComponentCombinators
import QLean.Generator.Implementation.ReversibleArithmeticCorrectness

/-!
# 可逆算術の作用中心strict階層component

基本可逆ゲートを末端componentとし、increment/decrementを一bit stepの再帰的`seq`合成から
構成する。親componentの`runBasis_correct`は子componentの公開fieldだけを使用し、既存の
幅全体回路定理を直接適用しない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

noncomputable section

/-- 可逆ゲート用の置換行列意味論。 -/
abbrev ReversibleGateBasisOperator {ancillaQubits systemQubits : Nat} :=
  (fun gate : ReversibleGate ancillaQubits systemQubits =>
    (reversibleGatePermutation gate).permMatrix ℂ)

/-- X/CNOT/Toffoliの計算基底置換は自己逆である。 -/
theorem reversibleGatePermutation_selfInverse
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits) :
    reversibleGatePermutation gate = (reversibleGatePermutation gate)⁻¹ := by
  apply Equiv.ext
  intro input
  cases gate <;> rfl

/-- X/CNOT/Toffoli一葉をpure基底置換へ結ぶ末端置換component族。 -/
def reversibleGatePermutationComponent
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits) :
    PermutationComponent
      (ReversibleGateBasisOperator
        (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))
      (reversibleGatePermutation
        (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := .gate gate
  reference := reversibleGatePermutation gate
  runBasis_correct := by intro input; rfl
  operator_correct := by
    change (reversibleGatePermutation gate).permMatrix ℂ =
      ((reversibleGatePermutation gate)⁻¹).permMatrix ℂ
    rw [← reversibleGatePermutation_selfInverse gate]

/-- 基本可逆ゲート一葉を全入力cleanなcomponentとして読む。 -/
def reversibleGateCleanComponent
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) :=
  CleanComponent.ofPermutation (reversibleGatePermutationComponent gate)

/-- 基本可逆ゲート一葉をPrimitiveGateへ写し、同じ解析置換行列をtargetとする。 -/
def reversibleGatePrimitiveExactOperatorComponent
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits) :
    ExactOperatorComponent
      (primitiveGateOperator : PrimitiveGate ancillaQubits systemQubits →
        Operator (JointBasis ancillaQubits systemQubits)) where
  circuit := .gate gate.toPrimitive
  target := (reversibleGatePermutation gate).permMatrix ℂ
  correct := by
    change primitiveGateOperator gate.toPrimitive =
      (reversibleGatePermutation gate).permMatrix ℂ
    exact (reversibleGate_operator_eq_primitive gate).symm

/-- 一stepが保証する、参照出力一致とscratch全復元。 -/
structure ControlledTargetXorScratchRestoration
    {ancillaQubits systemQubits : Nat}
    (scratches : List (Wire ancillaQubits systemQubits))
    (reference : JointBasis ancillaQubits systemQubits →
      JointBasis ancillaQubits systemQubits)
    (input output : JointBasis ancillaQubits systemQubits) : Prop where
  /-- 出力はpure参照作用そのものである。 -/
  output_eq : output = reference input
  /-- 全scratchは0へ戻る。 -/
  scratch_zero : ∀ wire ∈ scratches, output wire = false

/-- increment一bit stepの回路非依存な解析作用。 -/
def xorAllLowerBitsOneIntoBitReference
    {ancillaQubits systemQubits : Nat}
    (lower : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if allWiresTrue lower input then xBasisAction target input else input

/-- decrement一bit stepの回路非依存な解析作用。 -/
def xorAllLowerBitsZeroIntoBitReference
    {ancillaQubits systemQubits : Nat}
    (lower : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if boolControlsSatisfied (lower.map fun wire => (wire, false)) input then
    xBasisAction target input
  else input

/-- incrementの一bit多重制御反転をpure step作用とscratch復元へ結ぶ末端component。 -/
def verifiedXorAllLowerBitsOneIntoBitCleanComponent
    {ancillaQubits systemQubits : Nat}
    (lower scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (enoughScratch : lower.length ≤ scratches.length + 1)
    (layoutNodup : (lower ++ scratches ++ [target]).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorAllLowerBitsOneIntoBitCircuit lower scratches target
  reference := xorAllLowerBitsOneIntoBitReference lower target
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := ControlledTargetXorScratchRestoration scratches
    (xorAllLowerBitsOneIntoBitReference lower target)
  runBasis_correct := by
    intro input scratchZero
    simpa [xorAllLowerBitsOneIntoBitCircuit, xorAllLowerBitsOneIntoBitReference] using
      runBasis_positiveMultiControlledX lower scratches target input
        enoughScratch layoutNodup scratchZero
  outputCondition_correct := by
    intro input scratchZero wire member
    have wireDifferent : wire ≠ target := by
      intro equal
      have separated := (List.nodup_append.mp layoutNodup).2.2
      exact separated wire (List.mem_append_right lower member) target (by simp) equal
    unfold xorAllLowerBitsOneIntoBitReference
    split
    · rw [xBasisAction_other target wire wireDifferent]
      exact scratchZero wire member
    · exact scratchZero wire member
  restoration_correct := by
    intro input scratchZero
    refine ⟨rfl, ?_⟩
    intro wire member
    have wireDifferent : wire ≠ target := by
      intro equal
      have separated := (List.nodup_append.mp layoutNodup).2.2
      exact separated wire (List.mem_append_right lower member) target (by simp) equal
    unfold xorAllLowerBitsOneIntoBitReference
    split
    · rw [xBasisAction_other target wire wireDifferent]
      exact scratchZero wire member
    · exact scratchZero wire member

/-- decrementの一bit 0-control反転をpure step作用とscratch復元へ結ぶ末端component。 -/
def verifiedXorAllLowerBitsZeroIntoBitCleanComponent
    {ancillaQubits systemQubits : Nat}
    (lower scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (enoughScratch : lower.length ≤ scratches.length + 1)
    (layoutNodup : (lower ++ scratches ++ [target]).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorAllLowerBitsZeroIntoBitCircuit lower scratches target
  reference := xorAllLowerBitsZeroIntoBitReference lower target
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := ControlledTargetXorScratchRestoration scratches
    (xorAllLowerBitsZeroIntoBitReference lower target)
  runBasis_correct := by
    intro input scratchZero
    simpa [xorAllLowerBitsZeroIntoBitCircuit, xorAllLowerBitsZeroIntoBitReference] using
      runBasis_boolMultiControlledX (lower.map fun wire => (wire, false))
        scratches target input (by simpa using enoughScratch) (by
          simpa [List.map_map, Function.comp_def] using layoutNodup) scratchZero
  outputCondition_correct := by
    intro input scratchZero wire member
    have wireDifferent : wire ≠ target := by
      intro equal
      have separated := (List.nodup_append.mp layoutNodup).2.2
      exact separated wire (List.mem_append_right lower member) target (by simp) equal
    unfold xorAllLowerBitsZeroIntoBitReference
    split
    · rw [xBasisAction_other target wire wireDifferent]
      exact scratchZero wire member
    · exact scratchZero wire member
  restoration_correct := by
    intro input scratchZero
    refine ⟨rfl, ?_⟩
    intro wire member
    have wireDifferent : wire ≠ target := by
      intro equal
      have separated := (List.nodup_append.mp layoutNodup).2.2
      exact separated wire (List.mem_append_right lower member) target (by simp) equal
    unfold xorAllLowerBitsZeroIntoBitReference
    split
    · rw [xBasisAction_other target wire wireDifferent]
      exact scratchZero wire member
    · exact scratchZero wire member

/-- scratch を変えない空回路を、scratch clean 条件を保持する合成単位として包装する。 -/
def scratchIdentityCleanComponent
    {ancillaQubits systemQubits : Nat}
    (scratches : List (Wire ancillaQubits systemQubits)) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := .identity
  reference := id
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := fun input output => output = input
  runBasis_correct := by intro input _; rfl
  outputCondition_correct := by intro input scratchZero; exact scratchZero
  restoration_correct := by intro input _; rfl

/-- increment の各 bit step を `CleanComponent.seq` だけで帰納合成する部品族。 -/
def verifiedIncrementWordCarrySequenceCleanComponent
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) := by
  induction higher generalizing lower with
  | nil =>
      exact scratchIdentityCleanComponent scratches
  | cons target rest inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ rest).length ≤ scratches.length + 2 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          ((lower ++ [target]) ++ rest ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      have stepEnough : lower.length ≤ scratches.length + 1 := by
        simp only [List.length_append, List.length_cons] at enoughScratch
        omega
      have stepLayout : (lower ++ scratches ++ [target]).Nodup :=
        nodup_controls_scratches_target lower rest scratches target layoutNodup
      exact CleanComponent.seq
        (inductionHypothesis (lower := lower ++ [target]) recursiveEnough recursiveLayout)
        (verifiedXorAllLowerBitsOneIntoBitCleanComponent lower scratches target stepEnough stepLayout)

/-- increment の帰納 component の回路 AST は既存正本と定義的に一致する。 -/
theorem verifiedIncrementWordCarrySequenceCleanComponent_circuit
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup) :
    (verifiedIncrementWordCarrySequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).circuit =
      incrementWordCarrySequenceCircuit lower higher scratches := by
  induction higher generalizing lower with
  | nil => rfl
  | cons target rest inductionHypothesis =>
      change
        Circuit.seq
          (verifiedIncrementWordCarrySequenceCleanComponent (lower ++ [target]) rest scratches _ _).circuit
          (verifiedXorAllLowerBitsOneIntoBitCleanComponent lower scratches target _ _).circuit = _
      rw [inductionHypothesis (lower := lower ++ [target])]
      rfl

/-- increment の帰納 component の pure reference は既存の解析参照関数と一致する。 -/
theorem verifiedIncrementWordCarrySequenceCleanComponent_reference
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (input : JointBasis ancillaQubits systemQubits) :
    (verifiedIncrementWordCarrySequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).reference input =
      incrementWordCarrySequenceReference lower higher input := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target rest inductionHypothesis =>
      have stepEnough : lower.length ≤ scratches.length + 1 := by
        simp only [List.length_append, List.length_cons] at enoughScratch
        omega
      have stepLayout : (lower ++ scratches ++ [target]).Nodup :=
        nodup_controls_scratches_target lower rest scratches target layoutNodup
      change
        (verifiedXorAllLowerBitsOneIntoBitCleanComponent lower scratches target stepEnough stepLayout).reference
          ((verifiedIncrementWordCarrySequenceCleanComponent (lower ++ [target]) rest scratches _ _).reference input) = _
      rw [inductionHypothesis (lower := lower ++ [target])]
      rfl

/-- increment program の公開出力条件は、全 scratch が 0 という局所条件そのものである。 -/
theorem verifiedIncrementWordCarrySequenceCleanComponent_outputCondition
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (output : JointBasis ancillaQubits systemQubits) :
    (verifiedIncrementWordCarrySequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).outputCondition output ↔
      ∀ wire ∈ scratches, output wire = false := by
  cases higher <;> rfl

/-- clean scratch 入力は increment の帰納 component の合成入力条件を満たす。 -/
theorem verifiedIncrementWordCarrySequenceCleanComponent_accepts
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (input : JointBasis ancillaQubits systemQubits)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (verifiedIncrementWordCarrySequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).inputCondition input := by
  induction higher generalizing lower input with
  | nil => exact scratchZero
  | cons target rest inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ rest).length ≤ scratches.length + 2 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          ((lower ++ [target]) ++ rest ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      change
        (verifiedIncrementWordCarrySequenceCleanComponent (lower ++ [target]) rest scratches
          recursiveEnough recursiveLayout).inputCondition input ∧
        (verifiedXorAllLowerBitsOneIntoBitCleanComponent lower scratches target _ _).inputCondition
          ((verifiedIncrementWordCarrySequenceCleanComponent (lower ++ [target]) rest scratches
            recursiveEnough recursiveLayout).reference input)
      have recursiveClean := inductionHypothesis
        (lower := lower ++ [target]) recursiveEnough recursiveLayout
        (input := input) scratchZero
      refine ⟨recursiveClean, ?_⟩
      have restored :=
        (verifiedIncrementWordCarrySequenceCleanComponent (lower ++ [target]) rest scratches
          recursiveEnough recursiveLayout).outputCondition_correct input recursiveClean
      exact (verifiedIncrementWordCarrySequenceCleanComponent_outputCondition
        (lower ++ [target]) rest scratches recursiveEnough recursiveLayout _).mp restored

/-- decrement の各 bit step を `CleanComponent.seq` だけで帰納合成する部品族。 -/
def verifiedDecrementWordBorrowSequenceCleanComponent
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) := by
  induction higher generalizing lower with
  | nil =>
      exact scratchIdentityCleanComponent scratches
  | cons target rest inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ rest).length ≤ scratches.length + 2 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          ((lower ++ [target]) ++ rest ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      have stepEnough : lower.length ≤ scratches.length + 1 := by
        simp only [List.length_append, List.length_cons] at enoughScratch
        omega
      have stepLayout : (lower ++ scratches ++ [target]).Nodup :=
        nodup_controls_scratches_target lower rest scratches target layoutNodup
      exact CleanComponent.seq
        (inductionHypothesis (lower := lower ++ [target]) recursiveEnough recursiveLayout)
        (verifiedXorAllLowerBitsZeroIntoBitCleanComponent lower scratches target stepEnough stepLayout)

/-- decrement の帰納 component の回路 AST は既存正本と定義的に一致する。 -/
theorem verifiedDecrementWordBorrowSequenceCleanComponent_circuit
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup) :
    (verifiedDecrementWordBorrowSequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).circuit =
      decrementWordBorrowSequenceCircuit lower higher scratches := by
  induction higher generalizing lower with
  | nil => rfl
  | cons target rest inductionHypothesis =>
      change
        Circuit.seq
          (verifiedDecrementWordBorrowSequenceCleanComponent (lower ++ [target]) rest scratches _ _).circuit
          (verifiedXorAllLowerBitsZeroIntoBitCleanComponent lower scratches target _ _).circuit = _
      rw [inductionHypothesis (lower := lower ++ [target])]
      rfl

/-- decrement の帰納 component の pure reference は既存の解析参照関数と一致する。 -/
theorem verifiedDecrementWordBorrowSequenceCleanComponent_reference
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (input : JointBasis ancillaQubits systemQubits) :
    (verifiedDecrementWordBorrowSequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).reference input =
      decrementWordBorrowSequenceReference lower higher input := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target rest inductionHypothesis =>
      have stepEnough : lower.length ≤ scratches.length + 1 := by
        simp only [List.length_append, List.length_cons] at enoughScratch
        omega
      have stepLayout : (lower ++ scratches ++ [target]).Nodup :=
        nodup_controls_scratches_target lower rest scratches target layoutNodup
      change
        (verifiedXorAllLowerBitsZeroIntoBitCleanComponent lower scratches target stepEnough stepLayout).reference
          ((verifiedDecrementWordBorrowSequenceCleanComponent (lower ++ [target]) rest scratches _ _).reference input) = _
      rw [inductionHypothesis (lower := lower ++ [target])]
      simp only [verifiedXorAllLowerBitsZeroIntoBitCleanComponent, xorAllLowerBitsZeroIntoBitReference,
        decrementWordBorrowSequenceReference, boolControlsSatisfied_allFalse]

/-- decrement program の公開出力条件は、全 scratch が 0 という局所条件そのものである。 -/
theorem verifiedDecrementWordBorrowSequenceCleanComponent_outputCondition
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (output : JointBasis ancillaQubits systemQubits) :
    (verifiedDecrementWordBorrowSequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).outputCondition output ↔
      ∀ wire ∈ scratches, output wire = false := by
  cases higher <;> rfl

/-- clean scratch 入力は decrement の帰納 component の合成入力条件を満たす。 -/
theorem verifiedDecrementWordBorrowSequenceCleanComponent_accepts
    {ancillaQubits systemQubits : Nat}
    (lower higher scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 2)
    (layoutNodup : (lower ++ higher ++ scratches).Nodup)
    (input : JointBasis ancillaQubits systemQubits)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (verifiedDecrementWordBorrowSequenceCleanComponent lower higher scratches
      enoughScratch layoutNodup).inputCondition input := by
  induction higher generalizing lower input with
  | nil => exact scratchZero
  | cons target rest inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ rest).length ≤ scratches.length + 2 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          ((lower ++ [target]) ++ rest ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      change
        (verifiedDecrementWordBorrowSequenceCleanComponent (lower ++ [target]) rest scratches
          recursiveEnough recursiveLayout).inputCondition input ∧
        (verifiedXorAllLowerBitsZeroIntoBitCleanComponent lower scratches target _ _).inputCondition
          ((verifiedDecrementWordBorrowSequenceCleanComponent (lower ++ [target]) rest scratches
            recursiveEnough recursiveLayout).reference input)
      have recursiveClean := inductionHypothesis
        (lower := lower ++ [target]) recursiveEnough recursiveLayout
        (input := input) scratchZero
      refine ⟨recursiveClean, ?_⟩
      have restored :=
        (verifiedDecrementWordBorrowSequenceCleanComponent (lower ++ [target]) rest scratches
          recursiveEnough recursiveLayout).outputCondition_correct input recursiveClean
      exact (verifiedDecrementWordBorrowSequenceCleanComponent_outputCondition
        (lower ++ [target]) rest scratches recursiveEnough recursiveLayout _).mp restored

/-- word 周期算術の公開復元仕様。scratch 復元と解析的な word bit 列を同時に記録する。 -/
structure WordMod2PowInPlaceRestoration
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (expectedBits : List Bool)
    (input output : JointBasis ancillaQubits systemQubits) : Prop where
  /-- 全 scratch は 0 へ戻る。 -/
  scratch_zero : ∀ wire ∈ scratches, output wire = false
  /-- word の出力は独立な Bool 列計算と一致する。 -/
  word_bits : readWires word output = expectedBits

/-- increment program の子契約だけから、既存正本 AST と解析的周期 increment を結ぶ親部品。 -/
def verifiedIncrementWordMod2PowInPlaceCleanComponent
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := incrementWordMod2PowInPlaceCircuit word scratches
  reference := incrementWordMod2PowInPlaceReference word
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := fun input output =>
    WordMod2PowInPlaceRestoration word scratches
      (incrementBits (readWires word input)) input output
  runBasis_correct := by
    intro input scratchZero
    let program := verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
      enoughScratch layoutNodup
    have clean : program.inputCondition input :=
      verifiedIncrementWordCarrySequenceCleanComponent_accepts [] word scratches
        enoughScratch layoutNodup input scratchZero
    have childCorrect := program.runBasis_correct input clean
    rw [verifiedIncrementWordCarrySequenceCleanComponent_circuit [] word scratches
      enoughScratch layoutNodup] at childCorrect
    rw [verifiedIncrementWordCarrySequenceCleanComponent_reference [] word scratches
      enoughScratch layoutNodup input] at childCorrect
    simpa [incrementWordMod2PowInPlaceCircuit, incrementWordMod2PowInPlaceReference] using
      childCorrect
  outputCondition_correct := by
    intro input scratchZero
    have clean :
        (verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).inputCondition input :=
      verifiedIncrementWordCarrySequenceCleanComponent_accepts [] word scratches
        enoughScratch layoutNodup input scratchZero
    have childOutput :=
      (verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
        enoughScratch layoutNodup).outputCondition_correct input clean
    have scratchResult := (verifiedIncrementWordCarrySequenceCleanComponent_outputCondition [] word scratches
      enoughScratch layoutNodup
        ((verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).reference input)).mp childOutput
    rw [verifiedIncrementWordCarrySequenceCleanComponent_reference [] word scratches
      enoughScratch layoutNodup input] at scratchResult
    exact scratchResult
  restoration_correct := by
    intro input scratchZero
    have clean :
        (verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).inputCondition input :=
      verifiedIncrementWordCarrySequenceCleanComponent_accepts [] word scratches
        enoughScratch layoutNodup input scratchZero
    have childOutput :=
      (verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
        enoughScratch layoutNodup).outputCondition_correct input clean
    have scratchResult := (verifiedIncrementWordCarrySequenceCleanComponent_outputCondition
      [] word scratches enoughScratch layoutNodup
        ((verifiedIncrementWordCarrySequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).reference input)).mp childOutput
    rw [verifiedIncrementWordCarrySequenceCleanComponent_reference [] word scratches
      enoughScratch layoutNodup input] at scratchResult
    refine
      { scratch_zero := scratchResult
        word_bits := ?_ }
    simpa [incrementWordMod2PowInPlaceReference, incrementBits, allWiresTrue, readWires] using
      readWires_incrementWordCarrySequenceReference [] word input
        (List.nodup_append.mp layoutNodup).1

/-- decrement program の子契約だけから、既存正本 AST と解析的周期 decrement を結ぶ親部品。 -/
def verifiedDecrementWordMod2PowInPlaceCleanComponent
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := decrementWordMod2PowInPlaceCircuit word scratches
  reference := decrementWordMod2PowInPlaceReference word
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := fun input output =>
    WordMod2PowInPlaceRestoration word scratches
      (decrementBits (readWires word input)) input output
  runBasis_correct := by
    intro input scratchZero
    let program := verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
      enoughScratch layoutNodup
    have clean : program.inputCondition input :=
      verifiedDecrementWordBorrowSequenceCleanComponent_accepts [] word scratches
        enoughScratch layoutNodup input scratchZero
    have childCorrect := program.runBasis_correct input clean
    rw [verifiedDecrementWordBorrowSequenceCleanComponent_circuit [] word scratches
      enoughScratch layoutNodup] at childCorrect
    rw [verifiedDecrementWordBorrowSequenceCleanComponent_reference [] word scratches
      enoughScratch layoutNodup input] at childCorrect
    simpa [decrementWordMod2PowInPlaceCircuit, decrementWordMod2PowInPlaceReference] using
      childCorrect
  outputCondition_correct := by
    intro input scratchZero
    have clean :
        (verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).inputCondition input :=
      verifiedDecrementWordBorrowSequenceCleanComponent_accepts [] word scratches
        enoughScratch layoutNodup input scratchZero
    have childOutput :=
      (verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
        enoughScratch layoutNodup).outputCondition_correct input clean
    have scratchResult := (verifiedDecrementWordBorrowSequenceCleanComponent_outputCondition [] word scratches
      enoughScratch layoutNodup
        ((verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).reference input)).mp childOutput
    rw [verifiedDecrementWordBorrowSequenceCleanComponent_reference [] word scratches
      enoughScratch layoutNodup input] at scratchResult
    exact scratchResult
  restoration_correct := by
    intro input scratchZero
    have clean :
        (verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).inputCondition input :=
      verifiedDecrementWordBorrowSequenceCleanComponent_accepts [] word scratches
        enoughScratch layoutNodup input scratchZero
    have childOutput :=
      (verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
        enoughScratch layoutNodup).outputCondition_correct input clean
    have scratchResult := (verifiedDecrementWordBorrowSequenceCleanComponent_outputCondition
      [] word scratches enoughScratch layoutNodup
        ((verifiedDecrementWordBorrowSequenceCleanComponent [] word scratches
          enoughScratch layoutNodup).reference input)).mp childOutput
    rw [verifiedDecrementWordBorrowSequenceCleanComponent_reference [] word scratches
      enoughScratch layoutNodup input] at scratchResult
    refine
      { scratch_zero := scratchResult
        word_bits := ?_ }
    simpa [decrementWordMod2PowInPlaceReference, decrementBits, allWiresFalse, readWires] using
      readWires_decrementWordBorrowSequenceReference [] word input
        (List.nodup_append.mp layoutNodup).1

/-- xorEqualityIntoTargetCircuit 正本の回路から独立に定義した、target の条件付き反転作用。 -/
def xorEqualityIntoTargetAnalyticAction
    {ancillaQubits systemQubits : Nat}
    (left right : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if decide (readWires left input = readWires right input) then
    xBasisAction target input
  else input

/--
xorEqualityIntoTargetCircuit の既存基本ゲート列を独立な解析作用へ結ぶ compiled semantic leaf。
内部 compute/use/uncompute の子依存はこの contract では主張しない。
-/
def verifiedXorEqualityIntoTargetCleanComponent
    {ancillaQubits systemQubits : Nat}
    (left right flags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (leftLength : left.length = flags.length)
    (rightLength : right.length = flags.length)
    (leftDisjointFlags : left.Disjoint flags)
    (rightDisjointFlags : right.Disjoint flags)
    (flagsDisjointScratch : flags.Disjoint scratches)
    (flagsNodup : flags.Nodup)
    (positiveLayout : (flags ++ scratches ++ [target]).Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (enoughScratch : flags.length ≤ scratches.length + 1) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorEqualityIntoTargetCircuit left right flags scratches target
  reference := xorEqualityIntoTargetAnalyticAction left right target
  inputCondition := fun input =>
    readWires flags input = List.replicate flags.length false ∧
      ∀ wire ∈ scratches, input wire = false
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = xorEqualityIntoTargetAnalyticAction left right target input
  runBasis_correct := by
    intro input clean
    simpa [xorEqualityIntoTargetAnalyticAction] using
      runBasis_xorEqualityIntoTargetCircuit left right flags scratches target input
        leftLength rightLength leftDisjointFlags rightDisjointFlags
        flagsDisjointScratch flagsNodup positiveLayout targetAbsentLeft
        targetAbsentRight clean.1 clean.2 enoughScratch
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- less-than 正本の回路から独立に定義した、自然数比較による target 条件付き反転作用。 -/
def xorLessThanIntoTargetAnalyticAction
    {ancillaQubits systemQubits : Nat}
    (left right : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if decide (littleEndianNat (readWires left input) <
      littleEndianNat (readWires right input)) then
    xBasisAction target input
  else input

/--
一括 `Nodup` と scratch 幅から less-than 正本を包装する compiled semantic leaf。
内部 xorEqualityIntoTargetCircuit/step/fold の辺は、子 field だけの再証明がないため公開依存木に置かない。
-/
def verifiedXorLessThanIntoTargetCleanComponent
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (fullLayout :
      (left ++ right ++ equalFlags ++ scratches ++ [target]).Nodup)
    (scratchEnough : equalFlags.length ≤ scratches.length) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorLessThanIntoTargetCircuit left right equalFlags scratches target
  reference := xorLessThanIntoTargetAnalyticAction left right target
  inputCondition := fun input =>
    readWires equalFlags input = List.replicate equalFlags.length false ∧
      ∀ wire ∈ scratches, input wire = false
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = xorLessThanIntoTargetAnalyticAction left right target input
  runBasis_correct := by
    intro input clean
    simpa [xorLessThanIntoTargetAnalyticAction] using
      runBasis_xorLessThanIntoTargetCircuit_nat_of_layout left right equalFlags scratches target input
        leftLength rightLength fullLayout clean.1 clean.2 scratchEnough
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- 任意の可逆 permutation component を `toPrimitive` 後の exact operator component へ持ち上げる。 -/
def reversiblePermutationPrimitiveExactOperatorComponent
    {ancillaQubits systemQubits : Nat}
    (component : PermutationComponent
      (ReversibleGateBasisOperator
        (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))
      (reversibleGatePermutation
        (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))) :
    ExactOperatorComponent
      (primitiveGateOperator : PrimitiveGate ancillaQubits systemQubits →
        Operator (JointBasis ancillaQubits systemQubits)) :=
  ExactOperatorComponent.mapGates
    (ReversibleGateBasisOperator
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))
    primitiveGateOperator ReversibleGate.toPrimitive
    (fun gate => (reversibleGate_operator_eq_primitive gate).symm)
    component.toExactOperatorComponent

end

end ReversibleCircuit

end ProbabilityGeneratorQProof
