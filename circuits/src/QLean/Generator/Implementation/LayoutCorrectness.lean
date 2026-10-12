import QLean.Generator.Implementation.QTopLevel

/-!
# 型安全な連続レジスタ配置の一般補題

`RegisterSlice`が生成するwire列について、単射性、重複なし、systemとの非交差、
順に並ぶ二sliceの非交差を一度だけ証明する。個別回路ではこの一般結果を再利用する。
-/

namespace ProbabilityGeneratorQProof

namespace RegisterSlice

/-- 連続アンシラsliceに属する全wireを局所添字順に並べる。 -/
def wireList {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) :
    List (Wire ancillaWidth systemWidth) :=
  (List.finRange width).map slice.ancillaWire

/-- 一つのslice内の局所添字から全体アンシラwireへの写像は単射である。 -/
theorem ancillaWire_injective
    {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) :
    Function.Injective
      (slice.ancillaWire : Fin width → Wire ancillaWidth systemWidth) := by
  intro left right equal
  apply slice.index_injective
  exact Wire.ancilla.inj equal

/-- 一つの連続sliceが生成するwire列には重複がない。 -/
theorem wireList_nodup
    {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) :
    (slice.wireList : List (Wire ancillaWidth systemWidth)).Nodup := by
  exact List.Nodup.map (slice.ancillaWire_injective)
    (List.nodup_finRange width)

/-- slice wireの全体通し番号はslice開始位置と局所添字の和である。 -/
@[simp] theorem wireNumber_ancillaWire
    {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) (index : Fin width) :
    wireNumber (slice.ancillaWire index : Wire ancillaWidth systemWidth) =
      slice.start + index.val := by
  rfl

/-- system wire列と任意のアンシラslice wire列は互いに素である。 -/
theorem systemWires_disjoint_wireList
    {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) :
    ((List.finRange systemWidth).map
        (Wire.system : Fin systemWidth → Wire ancillaWidth systemWidth)).Disjoint
      (slice.wireList : List (Wire ancillaWidth systemWidth)) := by
  rw [List.disjoint_left]
  intro wire systemMember ancillaMember
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, rfl⟩
  rcases List.mem_map.mp ancillaMember with ⟨ancillaIndex, _, equal⟩
  cases equal

/-- 左sliceの末尾が右sliceの先頭以下なら、両sliceのwire列は互いに素である。 -/
theorem wireList_disjoint_of_end_le_start
    {ancillaWidth systemWidth leftWidth rightWidth : Nat}
    (left : RegisterSlice ancillaWidth leftWidth)
    (right : RegisterSlice ancillaWidth rightWidth)
    (separated : left.start + leftWidth ≤ right.start) :
    (left.wireList : List (Wire ancillaWidth systemWidth)).Disjoint
      (right.wireList : List (Wire ancillaWidth systemWidth)) := by
  rw [List.disjoint_left]
  intro wire leftMember rightMember
  rcases List.mem_map.mp leftMember with ⟨leftIndex, _, leftEqual⟩
  rcases List.mem_map.mp rightMember with ⟨rightIndex, _, rightEqual⟩
  rw [← leftEqual] at rightEqual
  have numbers := congrArg wireNumber rightEqual
  simp only [wireNumber_ancillaWire] at numbers
  omega

/-- 右sliceの末尾が左sliceの先頭以下の場合にも両sliceは互いに素である。 -/
theorem wireList_disjoint_of_start_ge_end
    {ancillaWidth systemWidth leftWidth rightWidth : Nat}
    (left : RegisterSlice ancillaWidth leftWidth)
    (right : RegisterSlice ancillaWidth rightWidth)
    (separated : right.start + rightWidth ≤ left.start) :
    (left.wireList : List (Wire ancillaWidth systemWidth)).Disjoint
      (right.wireList : List (Wire ancillaWidth systemWidth)) := by
  exact (right.wireList_disjoint_of_end_le_start left separated).symm

/-- 合成sliceの各wireは、その外側sliceのwire列にも含まれる。 -/
theorem compose_wireList_subset
    {total outerWidth innerWidth systemWidth : Nat}
    (outer : RegisterSlice total outerWidth)
    (inner : RegisterSlice outerWidth innerWidth) :
    ∀ {wire : Wire total systemWidth},
      wire ∈ (outer.compose inner).wireList → wire ∈ outer.wireList := by
  intro wire member
  rcases List.mem_map.mp member with ⟨innerIndex, _, rfl⟩
  let outerIndex : Fin outerWidth :=
    ⟨inner.start + innerIndex.val,
      lt_of_lt_of_le (Nat.add_lt_add_left innerIndex.isLt _) inner.fits⟩
  apply List.mem_map.mpr
  refine ⟨outerIndex, List.mem_finRange _, ?_⟩
  change Wire.ancilla (outer.index outerIndex) =
    Wire.ancilla ((outer.compose inner).index innerIndex)
  congr 1
  apply Fin.ext
  change outer.start + (inner.start + innerIndex.val) =
    outer.start + inner.start + innerIndex.val
  omega

end RegisterSlice

end ProbabilityGeneratorQProof
