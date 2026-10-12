import QLean.Generator.Implementation.QWriteSortedOutputCorrectness

/-!
# event回路と物理site更新の純粋参照接続

`2q` bitのsite wordに対する下位または上位`q` bitの周期incrementが、
物理格子上の右・上移動と一致することを、固定幅数値の一般恒等式で証明する。
全system基底や行列要素は列挙しない。
-/

namespace ProbabilityGeneratorQProof

open QParameters

namespace ReversibleCircuit

/-- siteを表す`2q` bit little-endian word。 -/
def siteWordBits (p : QParameters) (site : QSite p) : List Bool :=
  List.ofFn fun bit => siteBit p site bit

/-- site wordの長さは`2q`である。 -/
@[simp] theorem siteWordBits_length (p : QParameters) (site : QSite p) :
    (siteWordBits p site).length = p.wordWidth := by
  simp [siteWordBits]

/-- little-endian値は、下位列と上位列の連結に対して`low + 2^|low| high`に分解できる。 -/
theorem littleEndianNat_append (low high : List Bool) :
    littleEndianNat (low ++ high) =
      littleEndianNat low + 2 ^ low.length * littleEndianNat high := by
  induction low with
  | nil => simp [littleEndianNat]
  | cons bit low inductionHypothesis =>
      cases bit <;> simp [littleEndianNat, inductionHypothesis, pow_succ] <;> ring

/-- carry付きincrementはbit幅を変えない。 -/
@[simp] theorem incrementBitsWithCarry_length (carry : Bool) (bits : List Bool) :
    (incrementBitsWithCarry carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => simp [incrementBitsWithCarry]
  | cons bit bits inductionHypothesis =>
      simp [incrementBitsWithCarry, inductionHypothesis]

/-- 周期incrementはbit幅を変えない。 -/
@[simp] theorem incrementBits_length (bits : List Bool) :
    (incrementBits bits).length = bits.length := by
  simp [incrementBits]

/-- borrow付きdecrementはbit幅を変えない。 -/
@[simp] theorem decrementBitsWithBorrow_length (borrow : Bool) (bits : List Bool) :
    (decrementBitsWithBorrow borrow bits).length = bits.length := by
  induction bits generalizing borrow with
  | nil => simp [decrementBitsWithBorrow]
  | cons bit bits inductionHypothesis =>
      simp [decrementBitsWithBorrow, inductionHypothesis]

/-- 周期decrementはbit幅を変えない。 -/
@[simp] theorem decrementBits_length (bits : List Bool) :
    (decrementBits bits).length = bits.length := by
  simp [decrementBits]

/-- site word全体の自然数値はsite番号に一致する。 -/
theorem littleEndianNat_siteWordBits (p : QParameters) (site : QSite p) :
    littleEndianNat (siteWordBits p site) = site.val := by
  exact littleEndianNat_siteBits p site

/-- site番号は座標`(y,x)`の`y G + x`である。 -/
theorem site_val_eq_coordinates {p : QParameters} (site : QSite p) :
    site.val = (siteCoordinates site).1.val * p.G +
      (siteCoordinates site).2.val := by
  simp only [siteCoordinates, finProdFinEquiv_symm_apply]
  simpa [Nat.add_comm, Nat.mul_comm] using
    (Nat.mod_add_div site.val p.G).symm

/-- site wordの下位`q` bitは`x`座標を表す。 -/
theorem littleEndianNat_siteWordBits_take_q
    (p : QParameters) (site : QSite p) :
    littleEndianNat ((siteWordBits p site).take p.q) =
      (siteCoordinates site).2.val := by
  let bits := siteWordBits p site
  let low := bits.take p.q
  let high := bits.drop p.q
  have qLe : p.q ≤ bits.length := by
    simp only [bits, siteWordBits_length, QParameters.wordWidth]
    omega
  have lowLength : low.length = p.q := by simp [low, qLe]
  have split : low ++ high = bits := by
    exact List.take_append_drop p.q bits
  have fullValue : littleEndianNat bits = site.val := by
    simpa [bits] using littleEndianNat_siteWordBits p site
  have splitValue : site.val =
      littleEndianNat low + 2 ^ p.q * littleEndianNat high := by
    rw [← fullValue, ← split]
    rw [littleEndianNat_append, lowLength]
  have lowLt : littleEndianNat low < 2 ^ p.q := by
    simpa [lowLength] using littleEndianNat_lt_pow low
  have modulo := congrArg (fun value => value % (2 ^ p.q)) splitValue
  have lowValue : littleEndianNat low = site.val % (2 ^ p.q) := by
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lowLt] using modulo.symm
  have coordinateValue : (siteCoordinates site).2.val = site.val % p.G := by
    simp [siteCoordinates]
  exact lowValue.trans (by simpa [QParameters.G] using coordinateValue.symm)

/-- site wordの上位`q` bitは`y`座標を表す。 -/
theorem littleEndianNat_siteWordBits_drop_q
    (p : QParameters) (site : QSite p) :
    littleEndianNat ((siteWordBits p site).drop p.q) =
      (siteCoordinates site).1.val := by
  let bits := siteWordBits p site
  let low := bits.take p.q
  let high := bits.drop p.q
  have qLe : p.q ≤ bits.length := by
    simp only [bits, siteWordBits_length, QParameters.wordWidth]
    omega
  have lowLength : low.length = p.q := by simp [low, qLe]
  have split : low ++ high = bits := List.take_append_drop p.q bits
  have fullValue : littleEndianNat bits = site.val := by
    simpa [bits] using littleEndianNat_siteWordBits p site
  have splitValue : site.val =
      littleEndianNat low + 2 ^ p.q * littleEndianNat high := by
    rw [← fullValue, ← split]
    rw [littleEndianNat_append, lowLength]
  have lowLt : littleEndianNat low < 2 ^ p.q := by
    simpa [lowLength] using littleEndianNat_lt_pow low
  have divided := congrArg (fun value => value / (2 ^ p.q)) splitValue
  have powerPositive : 0 < 2 ^ p.q := pow_pos (by decide) _
  have highValue : littleEndianNat high = site.val / (2 ^ p.q) := by
    rw [Nat.add_mul_div_left _ _ powerPositive,
      Nat.div_eq_of_lt lowLt] at divided
    omega
  have coordinateValue : (siteCoordinates site).1.val = site.val / p.G := by
    simp [siteCoordinates]
  exact highValue.trans (by simpa [QParameters.G] using coordinateValue.symm)

/-- 右移動はsite wordの下位`q` bitだけの周期incrementである。 -/
theorem siteWordBits_moveSite_right (p : QParameters) (site : QSite p) :
    siteWordBits p (moveSite site .right) =
      incrementBits ((siteWordBits p site).take p.q) ++
        (siteWordBits p site).drop p.q := by
  apply littleEndianNat_injective_of_length_eq
  · simp [QParameters.wordWidth]
    omega
  · have movedCoordinates : siteCoordinates (moveSite site .right) =
        ((siteCoordinates site).1, incrementCoordinate (siteCoordinates site).2) := by
        simp [moveSite, siteCoordinates, siteOfCoordinates]
    have takeLength : ((siteWordBits p site).take p.q).length = p.q := by
      simp [QParameters.wordWidth]
      omega
    rw [littleEndianNat_siteWordBits]
    rw [site_val_eq_coordinates, movedCoordinates]
    rw [littleEndianNat_append, littleEndianNat_incrementBits]
    rw [littleEndianNat_siteWordBits_take_q,
      littleEndianNat_siteWordBits_drop_q]
    simp [incrementCoordinate, QParameters.G, takeLength]
    ring

/-- 上移動はsite wordの上位`q` bitだけの周期incrementである。 -/
theorem siteWordBits_moveSite_up (p : QParameters) (site : QSite p) :
    siteWordBits p (moveSite site .up) =
      (siteWordBits p site).take p.q ++
        incrementBits ((siteWordBits p site).drop p.q) := by
  apply littleEndianNat_injective_of_length_eq
  · simp [QParameters.wordWidth]
    omega
  · have movedCoordinates : siteCoordinates (moveSite site .up) =
        (incrementCoordinate (siteCoordinates site).1, (siteCoordinates site).2) := by
        simp [moveSite, siteCoordinates, siteOfCoordinates]
    have takeLength : ((siteWordBits p site).take p.q).length = p.q := by
      simp [QParameters.wordWidth]
      omega
    have dropLength : ((siteWordBits p site).drop p.q).length = p.q := by
      simp [QParameters.wordWidth]
      omega
    rw [littleEndianNat_siteWordBits]
    rw [site_val_eq_coordinates, movedCoordinates]
    rw [littleEndianNat_append, littleEndianNat_incrementBits]
    rw [littleEndianNat_siteWordBits_take_q,
      littleEndianNat_siteWordBits_drop_q]
    simp [incrementCoordinate, QParameters.G,
      takeLength, dropLength]
    ring

/-- 方向分岐をまとめたsite wordの周期increment仕様。 -/
theorem siteWordBits_moveSite (p : QParameters) (site : QSite p)
    (direction : QDirection) :
    siteWordBits p (moveSite site direction) =
      match direction with
      | .right => incrementBits ((siteWordBits p site).take p.q) ++
          (siteWordBits p site).drop p.q
      | .up => (siteWordBits p site).take p.q ++
          incrementBits ((siteWordBits p site).drop p.q) := by
  cases direction
  · exact siteWordBits_moveSite_right p site
  · exact siteWordBits_moveSite_up p site

/-- 座標decrementの値は、`G`を法とする`-1`の数値式に一致する。 -/
theorem decrementCoordinate_val {p : QParameters} (coordinate : Fin p.G) :
    (decrementCoordinate coordinate).val =
      (coordinate.val + p.G - 1) % p.G := by
  have sidePositive : 0 < p.G := by simp [QParameters.G]
  by_cases zero : coordinate.val = 0
  · have below : p.G - 1 < p.G := Nat.sub_lt sidePositive (by decide)
    simp [decrementCoordinate, zero, Nat.mod_eq_of_lt below]
  · have coordinatePositive : 0 < coordinate.val := Nat.pos_of_ne_zero zero
    have rearranged : coordinate.val + p.G - 1 =
        (coordinate.val - 1) + p.G := by omega
    simp only [decrementCoordinate, zero]
    change coordinate.val - 1 = (coordinate.val + p.G - 1) % p.G
    rw [rearranged, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega

/-- 右方向の逆移動はsite wordの下位`q` bitだけの周期decrementである。 -/
theorem siteWordBits_moveSiteBackward_right (p : QParameters) (site : QSite p) :
    siteWordBits p (moveSiteBackward site .right) =
      decrementBits ((siteWordBits p site).take p.q) ++
        (siteWordBits p site).drop p.q := by
  apply littleEndianNat_injective_of_length_eq
  · simp [QParameters.wordWidth]
    omega
  · have movedCoordinates : siteCoordinates (moveSiteBackward site .right) =
        ((siteCoordinates site).1, decrementCoordinate (siteCoordinates site).2) := by
        simp [moveSiteBackward, siteCoordinates, siteOfCoordinates]
    have takeLength : ((siteWordBits p site).take p.q).length = p.q := by
      simp [QParameters.wordWidth]
      omega
    rw [littleEndianNat_siteWordBits]
    rw [site_val_eq_coordinates, movedCoordinates]
    rw [littleEndianNat_append, littleEndianNat_decrementBits]
    rw [littleEndianNat_siteWordBits_take_q,
      littleEndianNat_siteWordBits_drop_q]
    rw [decrementCoordinate_val]
    simp [QParameters.G, takeLength]
    ring

/-- 上方向の逆移動はsite wordの上位`q` bitだけの周期decrementである。 -/
theorem siteWordBits_moveSiteBackward_up (p : QParameters) (site : QSite p) :
    siteWordBits p (moveSiteBackward site .up) =
      (siteWordBits p site).take p.q ++
        decrementBits ((siteWordBits p site).drop p.q) := by
  apply littleEndianNat_injective_of_length_eq
  · simp [QParameters.wordWidth]
    omega
  · have movedCoordinates : siteCoordinates (moveSiteBackward site .up) =
        (decrementCoordinate (siteCoordinates site).1, (siteCoordinates site).2) := by
        simp [moveSiteBackward, siteCoordinates, siteOfCoordinates]
    have takeLength : ((siteWordBits p site).take p.q).length = p.q := by
      simp [QParameters.wordWidth]
      omega
    have dropLength : ((siteWordBits p site).drop p.q).length = p.q := by
      simp [QParameters.wordWidth]
      omega
    rw [littleEndianNat_siteWordBits]
    rw [site_val_eq_coordinates, movedCoordinates]
    rw [littleEndianNat_append, littleEndianNat_decrementBits]
    rw [littleEndianNat_siteWordBits_take_q,
      littleEndianNat_siteWordBits_drop_q]
    rw [decrementCoordinate_val]
    simp [QParameters.G, takeLength, dropLength]
    ring

/-- 方向分岐をまとめたsite wordの周期decrement仕様。 -/
theorem siteWordBits_moveSiteBackward (p : QParameters) (site : QSite p)
    (direction : QDirection) :
    siteWordBits p (moveSiteBackward site direction) =
      match direction with
      | .right => decrementBits ((siteWordBits p site).take p.q) ++
          (siteWordBits p site).drop p.q
      | .up => (siteWordBits p site).take p.q ++
          decrementBits ((siteWordBits p site).drop p.q) := by
  cases direction
  · exact siteWordBits_moveSiteBackward_right p site
  · exact siteWordBits_moveSiteBackward_up p site

end ReversibleCircuit

end ProbabilityGeneratorQProof
