import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# Q回路最上位可逆部品の基底作用証明

systemとcolumn keyのCOPYを可逆XOR回路へ同定し、型安全なsliceの相異性から
register値と行列要素を一般幅のまま証明する。
-/

namespace ProbabilityGeneratorQProof

open QParameters

/-- COPY証明で使うsystem registerの全wire列。 -/
def topSystemWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map Wire.system

/-- COPY証明で使うcolumn key registerの全wire列。 -/
def topColumnKeyWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map (columnKeyWire p)

/-- system wire列の長さは物理system幅に等しい。 -/
@[simp] theorem topSystemWires_length (p : QParameters) :
    (topSystemWires p).length = p.systemWidth := by
  simp [topSystemWires]

/-- column key wire列の長さは物理system幅に等しい。 -/
@[simp] theorem topColumnKeyWires_length (p : QParameters) :
    (topColumnKeyWires p).length = p.systemWidth := by
  simp [topColumnKeyWires]

/-- column keyの添字から全体wireへの写像は単射である。 -/
theorem columnKeyWire_injective (p : QParameters) :
    Function.Injective (columnKeyWire p) := by
  intro left right equal
  apply (QLayout.canonical p).columnKey.index_injective
  exact Wire.ancilla.inj equal

/-- column key wire列には重複がない。 -/
theorem topColumnKeyWires_nodup (p : QParameters) :
    (topColumnKeyWires p).Nodup := by
  exact List.Nodup.map (columnKeyWire_injective p) (List.nodup_finRange _)

/-- system wire列には重複がない。 -/
theorem topSystemWires_nodup (p : QParameters) :
    (topSystemWires p).Nodup := by
  unfold topSystemWires
  exact List.Nodup.map (by
    intro left right equal
    exact Wire.system.inj equal) (List.nodup_finRange _)

/-- systemとcolumn keyは異なるregisterに属するため互いに素である。 -/
theorem topSystemWires_disjoint_topColumnKeyWires (p : QParameters) :
    (topSystemWires p).Disjoint (topColumnKeyWires p) := by
  rw [List.disjoint_left]
  intro wire systemMember keyMember
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, rfl⟩
  rcases List.mem_map.mp keyMember with ⟨keyIndex, _, equal⟩
  cases equal

/-- COPYの参照可逆回路は、対応するsystem/key wire間のXOR copyである。 -/
def xorSystemIntoColumnKeyReversibleCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  ReversibleCircuit.xorCopy (topSystemWires p) (topColumnKeyWires p)

/-- 正本COPY回路は参照可逆XOR回路の基本ゲート翻訳に構文的に等しい。 -/
theorem xorSystemIntoColumnKeyPrimitiveCircuit_eq_reversible (p : QParameters) :
    xorSystemIntoColumnKeyPrimitiveCircuit p =
      ReversibleCircuit.toPrimitive (xorSystemIntoColumnKeyReversibleCircuit p) := by
  let indices := List.finRange p.systemWidth
  change Circuit.fromList
      (indices.map fun index =>
        PrimitiveGate.cnot (.system index) (columnKeyWire p index) _) =
    Circuit.map ReversibleGate.toPrimitive
      (ReversibleCircuit.xorCopy
        (indices.map Wire.system) (indices.map (columnKeyWire p)))
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      have different :
          (Wire.system index : Wire p.ancillaWidth p.systemWidth) ≠
            columnKeyWire p index := by
        intro equal
        cases equal
      change
        Circuit.seq
            (.gate (.cnot (.system index) (columnKeyWire p index) _))
            (Circuit.fromList (indices.map fun tailIndex =>
              PrimitiveGate.cnot (.system tailIndex)
                (columnKeyWire p tailIndex) _)) =
          Circuit.seq
            (Circuit.map ReversibleGate.toPrimitive
              (ReversibleCircuit.safeCnot (.system index)
                (columnKeyWire p index)))
            (Circuit.map ReversibleGate.toPrimitive
              (ReversibleCircuit.xorCopy
                (indices.map Wire.system)
                (indices.map (columnKeyWire p))))
      simp [Circuit.map, ReversibleCircuit.safeCnot, different,
        inductionHypothesis]
      congr

/-- 正本COPYの理想行列は参照可逆回路の置換行列である。 -/
theorem xorSystemIntoColumnKeyPrimitiveCircuit_operator_eq_permMatrix (p : QParameters) :
    (xorSystemIntoColumnKeyPrimitiveCircuit p).toIdealOperator primitiveGateOperator =
      ((xorSystemIntoColumnKeyReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation).permMatrix ℂ := by
  rw [xorSystemIntoColumnKeyPrimitiveCircuit_eq_reversible]
  exact ReversibleCircuit.toPrimitive_operator_eq_permMatrix _

/-- false列とのbitwise XORは元のbit列に等しい。 -/
theorem zipWith_xor_false (bits : List Bool) :
    List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        bits (List.replicate bits.length false) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      cases bit <;>
        simp [List.replicate_succ, ← Nat.succ_eq_add_one, inductionHypothesis]

/-- keyが全0なら、COPY後のcolumn key値は入力system値に厳密一致する。 -/
theorem xorSystemIntoColumnKey_runBasis_key
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (keyZero :
      ReversibleCircuit.readWires (topColumnKeyWires p) input =
        List.replicate p.systemWidth false) :
    ReversibleCircuit.readWires (topColumnKeyWires p)
        ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
          reversibleGatePermutation input) =
      ReversibleCircuit.readWires (topSystemWires p) input := by
  rw [xorSystemIntoColumnKeyReversibleCircuit]
  rw [readWires_validatedXorCopyLists_target
    (topSystemWires p) (topColumnKeyWires p) input
    (topSystemWires_nodup p) (topColumnKeyWires_nodup p)]
  · rw [keyZero]
    have sourceLength :
        (ReversibleCircuit.readWires (topSystemWires p) input).length =
          p.systemWidth := by
      simp [ReversibleCircuit.readWires]
    have replicateLength :
        List.replicate p.systemWidth false =
          List.replicate
            (ReversibleCircuit.readWires (topSystemWires p) input).length false := by
      rw [sourceLength]
    rw [replicateLength]
    exact zipWith_xor_false _
  · simp
  · exact topSystemWires_disjoint_topColumnKeyWires p

/-- 正本COPYの行列要素は参照`runBasis`が作る一個の出力でだけ1になる。 -/
theorem xorSystemIntoColumnKey_basisAmplitude
    (p : QParameters)
    (input output : JointBasis p.ancillaWidth p.systemWidth) :
    (xorSystemIntoColumnKeyPrimitiveCircuit p).toIdealOperator primitiveGateOperator output input =
      if output =
          (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
            reversibleGatePermutation input then 1 else 0 := by
  rw [xorSystemIntoColumnKeyPrimitiveCircuit_eq_reversible]
  exact reversibleCircuit_basisAmplitude _ _ _

end ProbabilityGeneratorQProof
