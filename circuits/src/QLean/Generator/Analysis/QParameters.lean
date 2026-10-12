import QLean.Generator.Analysis.Registers
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

-- このmoduleは回路実装から独立したQ parameterとwire layoutだけを定義する。

/-!
# 一般Q回路のパラメータと型安全なレジスタ配置

技術レポートの`G = 2^q`、delimiter幅、selector幅、および最上位回路の全レジスタを
Leanの型に固定する。各部分レジスタは全体幅に収まる証明を持つため、範囲外wireを
構成できない。
-/

namespace ProbabilityGeneratorQProof

/-- 一般Q回路に必要な格子bit幅と最大粒子数、およびそれらの正値証明。 -/
structure QParameters where
  /-- 格子の一座標を表す量子ビット数。 -/
  q : Nat
  /-- 配置に許す最大粒子数。 -/
  K : Nat
  /-- 座標bit幅は正である。 -/
  q_pos : 0 < q
  /-- 最大粒子数は正である。 -/
  K_pos : 0 < K
deriving Repr

namespace QParameters

/-- 周期格子の一辺`G = 2^q`。 -/
def G (p : QParameters) : Nat := 2 ^ p.q

/-- 一つのsiteを表すword幅`2q`。 -/
def wordWidth (p : QParameters) : Nat := 2 * p.q

/-- delimiter符号を格納するsystem幅`2qK + 1`。 -/
def systemWidth (p : QParameters) : Nat := p.wordWidth * p.K + 1

/-- 固定幅selectorに含まれる有効branch数`6K`。 -/
def selectorCount (p : QParameters) : Nat := 6 * p.K

/-- `6K`個の値を保持するselector幅`ceil(log₂(6K))`。 -/
def selectorWidth (p : QParameters) : Nat := Nat.clog 2 p.selectorCount

/-- bitonic sortへ渡す2冪個のword数。 -/
def sortWordCount (p : QParameters) : Nat := 2 ^ Nat.clog 2 p.K

/-- selector数は正である。 -/
theorem selectorCount_pos (p : QParameters) : 0 < p.selectorCount := by
  simp [selectorCount, p.K_pos]

/-- selector幅のbit列には全`6K` selectorが収まる。 -/
theorem selectorCount_le_capacity (p : QParameters) :
    p.selectorCount ≤ 2 ^ p.selectorWidth := by
  exact Nat.le_pow_clog (by decide) p.selectorCount

/-- sort用word数には全`K` slotが収まる。 -/
theorem K_le_sortWordCount (p : QParameters) : p.K ≤ p.sortWordCount := by
  exact Nat.le_pow_clog (by decide) p.K

/-- sort用word数は正である。 -/
theorem sortWordCount_pos (p : QParameters) : 0 < p.sortWordCount := by
  simp [sortWordCount]

/-- compact decoderのdegree one-hot領域幅。 -/
def degreeWidth (p : QParameters) : Nat := p.K

/-- 各slotの存在flag領域幅。 -/
def presentWidth (p : QParameters) : Nat := p.K

/-- moved siteを保持する領域幅。 -/
def movedWidth (p : QParameters) : Nat := p.wordWidth

/-- marker付きcandidate word列の領域幅。 -/
def candidateWidth (p : QParameters) : Nat :=
  p.sortWordCount * (p.wordWidth + 1)

/--
compare--controlled-swapの履歴flag幅。
`word × stage × distance`を衝突なく符号化できる保守的な積幅を確保する。
-/
def sortFlagWidth (p : QParameters) : Nat :=
  p.sortWordCount * (Nat.clog 2 p.K + 1) * (Nat.clog 2 p.K + 1)

/-- membershipの等値flag領域幅。 -/
def membershipEqWidth (p : QParameters) : Nat := p.K

/-- membershipの有効一致flag領域幅。 -/
def membershipGoodWidth (p : QParameters) : Nat := p.K

/-- sorted位置一致flag領域幅。 -/
def positionMatchWidth (p : QParameters) : Nat := p.K

/-- sourceとsorted位置のpair flag領域幅。 -/
def pairWidth (p : QParameters) : Nat := p.K

/-- 多重ANDを二入力Toffoliへ分解する一時領域幅。 -/
def andWorkWidth (p : QParameters) : Nat :=
  4 * p.K + 16 + p.selectorWidth + p.wordWidth

/-- 比較器と周期加減算で共有するborrow領域幅。 -/
def borrowWidth (p : QParameters) : Nat := p.wordWidth

/-- oracle内部workの各領域を直列配置した総幅。 -/
def oracleWorkWidth (p : QParameters) : Nat :=
  p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
    p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
    p.membershipGoodWidth + 1 + 1 + 1 + p.positionMatchWidth + p.pairWidth +
    p.wordWidth + p.andWorkWidth + p.borrowWidth

/-- 最上位Q回路のsignalとworkを合わせたアンシラ総幅。 -/
def ancillaWidth (p : QParameters) : Nat :=
  2 * p.systemWidth + 3 * p.selectorWidth + 4 + p.oracleWorkWidth

/-- 外部回路へ配置するときに保持する、oracle workより前のsignal幅。 -/
def generatorSignalWidth (p : QParameters) : Nat :=
  2 * p.systemWidth + 3 * p.selectorWidth + 4

/-- 外部回路の共有work領域へ配置する、Q oracle内部work幅。 -/
def generatorWorkWidth (p : QParameters) : Nat := p.oracleWorkWidth

/-- Q system registerを外部回路のdata registerとして配置するときの幅。 -/
def generatorDataWidth (p : QParameters) : Nat := p.systemWidth

/-- canonical Q ancillaはsignal prefixとoracle-work suffixへ隙間なく分かれる。 -/
@[simp] theorem generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth
    (p : QParameters) :
    p.generatorSignalWidth + p.generatorWorkWidth = p.ancillaWidth := by
  rfl

/-- canonical Q system幅は外部配置で使うdata幅そのものである。 -/
@[simp] theorem generatorDataWidth_eq_systemWidth (p : QParameters) :
    p.generatorDataWidth = p.systemWidth := by
  rfl

/-- Width-only contract for placing the canonical Q source into an external
`signal ++ work ++ data` register order. -/
structure ProbabilityGeneratorCanonicalPlacementWidths
    (p : QParameters) (signalWidth workWidth dataWidth : Nat) : Prop where
  signal_eq : signalWidth = p.generatorSignalWidth
  work_eq : workWidth = p.generatorWorkWidth
  data_eq : dataWidth = p.generatorDataWidth

/-- Canonical widths satisfy the external placement contract definitionally. -/
theorem ProbabilityGeneratorCanonicalPlacementWidths.canonical (p : QParameters) :
    ProbabilityGeneratorCanonicalPlacementWidths p
      p.generatorSignalWidth p.generatorWorkWidth p.generatorDataWidth := by
  exact {
    signal_eq := rfl
    work_eq := rfl
    data_eq := rfl
  }

/-- The width-only placement contract covers the complete canonical Q source. -/
theorem ProbabilityGeneratorCanonicalPlacementWidths.sourceWidth_eq
    {p : QParameters} {signalWidth workWidth dataWidth : Nat}
    (widths : ProbabilityGeneratorCanonicalPlacementWidths
      p signalWidth workWidth dataWidth) :
    p.ancillaWidth + p.systemWidth =
      signalWidth + workWidth + dataWidth := by
  rcases widths with ⟨rfl, rfl, rfl⟩
  rw [generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth,
    generatorDataWidth_eq_systemWidth]

end QParameters

/-- 全体幅`total`内の連続した`width`本のwireを表す、境界証明付きslice。 -/
structure RegisterSlice (total width : Nat) where
  /-- sliceの先頭offset。 -/
  start : Nat
  /-- slice末尾が全体幅を越えないことの証明。 -/
  fits : start + width ≤ total

namespace RegisterSlice

/-- slice内の型安全な添字を、全体レジスタの型安全な添字へ埋め込む。 -/
def index {total width : Nat} (slice : RegisterSlice total width) (localIndex : Fin width) :
    Fin total :=
  ⟨slice.start + localIndex.val,
    lt_of_lt_of_le (Nat.add_lt_add_left localIndex.isLt _) slice.fits⟩

/-- sliceによる全体レジスタへの埋込みは単射である。 -/
theorem index_injective {total width : Nat} (slice : RegisterSlice total width) :
    Function.Injective slice.index := by
  intro left right equal
  apply Fin.ext
  have := congrArg Fin.val equal
  simp [index] at this
  omega

/-- アンシラslice内の添字を、型安全なQ回路wireへ変換する。 -/
def ancillaWire {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) (localIndex : Fin width) :
    Wire ancillaWidth systemWidth :=
  .ancilla (slice.index localIndex)

/-- 外側sliceの中にある内側sliceを、全体レジスタ上のsliceへ合成する。 -/
def compose {total outerWidth innerWidth : Nat}
    (outer : RegisterSlice total outerWidth)
    (inner : RegisterSlice outerWidth innerWidth) : RegisterSlice total innerWidth where
  start := outer.start + inner.start
  fits := by
    calc
      outer.start + inner.start + innerWidth =
          outer.start + (inner.start + innerWidth) := by omega
      _ ≤ outer.start + outerWidth := Nat.add_le_add_left inner.fits _
      _ ≤ total := outer.fits

end RegisterSlice

/-- oracle内部workを、用途ごとに相異なる型付きsliceへ分割した配置。 -/
structure OracleWorkLayout (p : QParameters) where
/-- degreeをone-hot形式で表す。 -/
  degree : RegisterSlice p.oracleWorkWidth p.degreeWidth
  /-- delimiter合法性flag。 -/
  legal : RegisterSlice p.oracleWorkWidth 1
  /-- 各slotの存在flag。 -/
  present : RegisterSlice p.oracleWorkWidth p.presentWidth
  /-- degree境界条件flag。 -/
  degreeCondition : RegisterSlice p.oracleWorkWidth 1
  /-- 負制御を正制御へ変換するときの定数1。 -/
  constantOne : RegisterSlice p.oracleWorkWidth 1
  /-- selector等値比較の結果。 -/
  selected : RegisterSlice p.oracleWorkWidth 1
  /-- 移動前後siteの一時word。 -/
  moved : RegisterSlice p.oracleWorkWidth p.movedWidth
  /-- marker付きcandidate word列。 -/
  candidate : RegisterSlice p.oracleWorkWidth p.candidateWidth
  /-- bitonic comparatorのswap履歴。 -/
  sortFlags : RegisterSlice p.oracleWorkWidth p.sortFlagWidth
  /-- membershipのword等値flag。 -/
  membershipEqual : RegisterSlice p.oracleWorkWidth p.membershipEqWidth
  /-- membershipのpresentと等値を合わせたflag。 -/
  membershipGood : RegisterSlice p.oracleWorkWidth p.membershipGoodWidth
  /-- candidateが既存配置に含まれないことを示すflag。 -/
  absent : RegisterSlice p.oracleWorkWidth 1
  /-- 選択slot以外にcandidateが存在することを示すflag。 -/
  presentOther : RegisterSlice p.oracleWorkWidth 1
  /-- 現在branchがactiveであることを示すflag。 -/
  branch : RegisterSlice p.oracleWorkWidth 1
  /-- sorted wordと目的siteの一致flag。 -/
  positionMatch : RegisterSlice p.oracleWorkWidth p.positionMatchWidth
  /-- source slotとsorted slotの組を示すflag。 -/
  pair : RegisterSlice p.oracleWorkWidth p.pairWidth
  /-- word等値・大小比較のbit単位work。 -/
  compareWork : RegisterSlice p.oracleWorkWidth p.wordWidth
  /-- 多重制御ANDの中間値。 -/
  andWork : RegisterSlice p.oracleWorkWidth p.andWorkWidth
  /-- 比較器・周期加減算のborrow/carry。 -/
  borrow : RegisterSlice p.oracleWorkWidth p.borrowWidth

namespace OracleWorkLayout

/-- 技術レポートの順序どおりにoracle workを隙間なく割り当てる。 -/
def canonical (p : QParameters) : OracleWorkLayout p where
  degree := ⟨0, by simp [QParameters.oracleWorkWidth]; omega⟩
  legal := ⟨p.degreeWidth, by simp [QParameters.oracleWorkWidth]; omega⟩
  present := ⟨p.degreeWidth + 1, by simp [QParameters.oracleWorkWidth]; omega⟩
  degreeCondition := ⟨p.degreeWidth + 1 + p.presentWidth,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  constantOne := ⟨p.degreeWidth + 1 + p.presentWidth + 1,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  selected := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  moved := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  candidate := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  sortFlags := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth, by simp [QParameters.oracleWorkWidth]; omega⟩
  membershipEqual := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  membershipGood := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  absent := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth, by simp [QParameters.oracleWorkWidth]; omega⟩
  presentOther := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1, by simp [QParameters.oracleWorkWidth]; omega⟩
  branch := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1 + 1,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  positionMatch := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1 + 1 + 1,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  pair := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1 + 1 + 1 + p.positionMatchWidth,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  compareWork := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1 + 1 + 1 + p.positionMatchWidth + p.pairWidth,
    by simp [QParameters.oracleWorkWidth]; omega⟩
  andWork := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1 + 1 + 1 + p.positionMatchWidth + p.pairWidth +
      p.wordWidth, by simp [QParameters.oracleWorkWidth]⟩
  borrow := ⟨p.degreeWidth + 1 + p.presentWidth + 1 + 1 + 1 + p.movedWidth +
      p.candidateWidth + p.sortFlagWidth + p.membershipEqWidth +
      p.membershipGoodWidth + 1 + 1 + 1 + p.positionMatchWidth + p.pairWidth +
      p.wordWidth + p.andWorkWidth,
    by simp [QParameters.oracleWorkWidth]⟩

end OracleWorkLayout

/-- 最上位Q回路のsystem・signal・workを型安全に割り当てた正本layout。 -/
structure QLayout (p : QParameters) where
  /-- column keyとして保持する更新前配置。 -/
  columnKey : RegisterSlice p.ancillaWidth p.systemWidth
  /-- row側selector。 -/
  rowSelector : RegisterSlice p.ancillaWidth p.selectorWidth
  /-- column側selector。 -/
  columnSelector : RegisterSlice p.ancillaWidth p.selectorWidth
  /-- row/column key一致を検査するsignal。 -/
  keySignal : RegisterSlice p.ancillaWidth 1
  /-- activeと符号を振幅へ変換するsignal。 -/
  amplitudeSignal : RegisterSlice p.ancillaWidth 1
  /-- column oracleが返す更新後配置。 -/
  rowOutput : RegisterSlice p.ancillaWidth p.systemWidth
  /-- oracleが返す出力selector。 -/
  selectorOutput : RegisterSlice p.ancillaWidth p.selectorWidth
  /-- column branchの負号bit。 -/
  negative : RegisterSlice p.ancillaWidth 1
  /-- oracle branchのactive bit。 -/
  active : RegisterSlice p.ancillaWidth 1
  /-- compute--use--uncompute内だけで使うoracle work全体。 -/
  oracleWork : RegisterSlice p.ancillaWidth p.oracleWorkWidth
  /-- oracle work内部の用途別layout。 -/
  oracle : OracleWorkLayout p

namespace QLayout

/-- 技術レポートの式に一致する、隙間のない最上位レジスタ配置。 -/
def canonical (p : QParameters) : QLayout p where
  columnKey := ⟨0, by simp [QParameters.ancillaWidth]; omega⟩
  rowSelector := ⟨p.systemWidth, by simp [QParameters.ancillaWidth]; omega⟩
  columnSelector := ⟨p.systemWidth + p.selectorWidth,
    by simp [QParameters.ancillaWidth]; omega⟩
  keySignal := ⟨p.systemWidth + 2 * p.selectorWidth,
    by simp [QParameters.ancillaWidth]; omega⟩
  amplitudeSignal := ⟨p.systemWidth + 2 * p.selectorWidth + 1,
    by simp [QParameters.ancillaWidth]; omega⟩
  rowOutput := ⟨p.systemWidth + 2 * p.selectorWidth + 2,
    by simp [QParameters.ancillaWidth]; omega⟩
  selectorOutput := ⟨2 * p.systemWidth + 2 * p.selectorWidth + 2,
    by simp [QParameters.ancillaWidth]; omega⟩
  negative := ⟨2 * p.systemWidth + 3 * p.selectorWidth + 2,
    by simp [QParameters.ancillaWidth]; omega⟩
  active := ⟨2 * p.systemWidth + 3 * p.selectorWidth + 3,
    by simp [QParameters.ancillaWidth]⟩
  oracleWork := ⟨2 * p.systemWidth + 3 * p.selectorWidth + 4,
    by simp [QParameters.ancillaWidth]⟩
  oracle := OracleWorkLayout.canonical p

/-- system registerの型安全なwireを得る。 -/
def systemWire (p : QParameters) (index : Fin p.systemWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  .system index

/-- 任意のアンシラsliceを現在のQ回路のwireへ埋め込む。 -/
def ancillaWire {p : QParameters} {width : Nat}
    (slice : RegisterSlice p.ancillaWidth width) (index : Fin width) :
    Wire p.ancillaWidth p.systemWidth :=
  slice.ancillaWire index

/-- oracle内部の相対sliceを最上位アンシラ全体のsliceへ持ち上げる。 -/
def oracleSlice {p : QParameters} {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width) :
    RegisterSlice p.ancillaWidth width :=
  (QLayout.canonical p).oracleWork.compose slice

/-- Canonical Q source ancillaを、外部配置のsignal prefixとwork suffixへ
分解した二slice bundle。 -/
structure GeneratorSourceSlices (p : QParameters) where
  signal : RegisterSlice p.ancillaWidth p.generatorSignalWidth
  work : RegisterSlice p.ancillaWidth p.generatorWorkWidth
  signal_start : signal.start = 0
  work_start : work.start = p.generatorSignalWidth

/-- `QLayout.canonical`の既存offsetをそのまま公開するsource slice分解。 -/
def canonicalGeneratorSourceSlices (p : QParameters) :
    GeneratorSourceSlices p where
  signal := ⟨0, by
    rw [← p.generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth]
    omega⟩
  work := (QLayout.canonical p).oracleWork
  signal_start := rfl
  work_start := by
    rfl

end QLayout

/-- 任意の物理system基底に、全0アンシラを結合したQ回路の標準入力基底。 -/
def zeroAncillaJointBasis (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  combineBasis (allZeroAncilla p.ancillaWidth) system

/-- 標準入力基底では任意のアンシラwireが0である。 -/
@[simp] theorem zeroAncillaJointBasis_ancilla
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (index : Fin p.ancillaWidth) :
    zeroAncillaJointBasis p system (.ancilla index) = false := by
  rfl

/-- 標準入力基底のsystem wireは、与えた物理system基底をそのまま保持する。 -/
@[simp] theorem zeroAncillaJointBasis_system
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (index : Fin p.systemWidth) :
    zeroAncillaJointBasis p system (.system index) = system index := by
  rfl

end ProbabilityGeneratorQProof
