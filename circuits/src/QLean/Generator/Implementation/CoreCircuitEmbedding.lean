import QLean.Generator.Implementation.UQCircuit
import Lean.Data.Json

/-!
# Q固有回路から共有core ASTへの型安全な埋込み

Q固有のancilla/system wireを `Fin (ancilla+system)` へ標準化し、さらに任意の大きい
`Fin totalQubits` へinjectiveに配置する。結果は `VerifiedCircuitCore.PrimitiveGate` だけを葉に
持つ共有 `Circuit` であり、424-wire等の統一ASTへそのまま挿入できる。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Q固有wireを、ancillaを先、systemを後に並べた標準数値wireへ写す。 -/
def wireToCanonicalFin {ancillaQubits systemQubits : Nat} :
    Wire ancillaQubits systemQubits → Fin (ancillaQubits + systemQubits)
  | .ancilla index =>
      ⟨index, Nat.lt_add_right systemQubits index.isLt⟩
  | .system index =>
      ⟨ancillaQubits + index,
        Nat.add_lt_add_left index.isLt ancillaQubits⟩

/-- 標準数値化はwireの所属と添字を失わない。 -/
theorem wireToCanonicalFin_injective {ancillaQubits systemQubits : Nat} :
    Function.Injective
      (wireToCanonicalFin (ancillaQubits := ancillaQubits)
        (systemQubits := systemQubits)) := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [wireToCanonicalFin, Fin.ext_iff] <;> omega

/-- Q全wireと標準 `Fin (ancilla+system)` の間のinjective embedding。 -/
def canonicalQWireEmbedding (ancillaQubits systemQubits : Nat) :
    Wire ancillaQubits systemQubits ↪ Fin (ancillaQubits + systemQubits) where
  toFun := wireToCanonicalFin
  inj' := wireToCanonicalFin_injective

/-- Q回路を大きい共有registerへ置くinjectiveなwire配置。 -/
structure QWireEmbedding (ancillaQubits systemQubits totalQubits : Nat) where
  /-- 標準Q wireから統一register wireへの配置。 -/
  placement : Fin (ancillaQubits + systemQubits) ↪ Fin totalQubits

namespace QWireEmbedding

/-- Q固有wireを統一registerへ直接写す合成embedding。 -/
def placedWire {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits) :
    Wire ancillaQubits systemQubits ↪ Fin totalQubits :=
  (canonicalQWireEmbedding ancillaQubits systemQubits).trans embedding.placement

/-- 異なるQ wireは統一register上でも異なる。 -/
theorem placedWire_ne {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    {left right : Wire ancillaQubits systemQubits} (different : left ≠ right) :
    embedding.placedWire left ≠ embedding.placedWire right := by
  exact fun equal => different (embedding.placedWire.injective equal)

/-- ancilla像とsystem像は統一register上で交わらない。 -/
theorem ancilla_ne_system {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (ancilla : Fin ancillaQubits) (system : Fin systemQubits) :
    embedding.placedWire (.ancilla ancilla) ≠ embedding.placedWire (.system system) := by
  apply placedWire_ne embedding
  intro equal
  cases equal

end QWireEmbedding

/-- Qの記号角度構文を、木構造を失わず共有core角度構文へ再帰的に移す。 -/
def AngleExpr.toCore : AngleExpr → VerifiedCircuitCore.AngleExpr
  | .rational value => .rational value.num value.den value.den_pos
  | .pi => .pi
  | .sqrt value => .sqrt value.toCore
  | .acos value => .acos value.toCore
  | .add left right => .add left.toCore right.toCore
  | .mul left right => .mul left.toCore right.toCore
  | .neg value => .neg value.toCore

/-- 角度構文の再帰移行は任意のsymbol環境で厳密実数解釈を保存する。 -/
@[simp] theorem AngleExpr.toCore_eval (angle : AngleExpr)
    (symbolValue : String → ℝ) :
    angle.toCore.eval symbolValue = angle.toReal := by
  induction angle with
  | rational value =>
      simp [AngleExpr.toCore, VerifiedCircuitCore.AngleExpr.eval,
        AngleExpr.toReal, Rat.cast_def]
  | pi => rfl
  | sqrt value inductionHypothesis =>
      simp [AngleExpr.toCore, VerifiedCircuitCore.AngleExpr.eval,
        AngleExpr.toReal, inductionHypothesis]
  | acos value inductionHypothesis =>
      simp [AngleExpr.toCore, VerifiedCircuitCore.AngleExpr.eval,
        AngleExpr.toReal, inductionHypothesis]
  | add left right leftInduction rightInduction =>
      simp [AngleExpr.toCore, VerifiedCircuitCore.AngleExpr.eval,
        AngleExpr.toReal, leftInduction, rightInduction]
  | mul left right leftInduction rightInduction =>
      simp [AngleExpr.toCore, VerifiedCircuitCore.AngleExpr.eval,
        AngleExpr.toReal, leftInduction, rightInduction]
  | neg value inductionHypothesis =>
      simp [AngleExpr.toCore, AngleExpr.toReal, inductionHypothesis]

/-- Q固有基本gateを標準幅の共有core基本gateへcompileする。 -/
def PrimitiveGate.toCanonicalCore {ancillaQubits systemQubits : Nat} :
    PrimitiveGate ancillaQubits systemQubits →
      VerifiedCircuitCore.PrimitiveGate (ancillaQubits + systemQubits)
  | .x target => .x (wireToCanonicalFin target)
  | .h target => .h (wireToCanonicalFin target)
  | .ry target angle => .ry angle.toCore (wireToCanonicalFin target)
  | .cnot control target different =>
      .cnot (wireToCanonicalFin control) (wireToCanonicalFin target)
        (fun equal => different (wireToCanonicalFin_injective equal))
  | .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      .toffoli (wireToCanonicalFin control₁) (wireToCanonicalFin control₂)
        (wireToCanonicalFin target)
        (fun equal => controlsDifferent (wireToCanonicalFin_injective equal))
        (fun equal => firstDifferent (wireToCanonicalFin_injective equal))
        (fun equal => secondDifferent (wireToCanonicalFin_injective equal))

/-- Q固有基本gateを指定した大register位置へcompileする。 -/
def PrimitiveGate.toEmbeddedCore
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits) :
    PrimitiveGate ancillaQubits systemQubits →
      VerifiedCircuitCore.PrimitiveGate totalQubits :=
  VerifiedCircuitCore.PrimitiveGate.mapWires embedding.placement ∘
    PrimitiveGate.toCanonicalCore

/-- 任意のQ固有回路を、指定した統一register上の共有core ASTへcompileする。 -/
def compileCircuitToCore
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate totalQubits) :=
  VerifiedCircuitCore.Circuit.mapGates
    (PrimitiveGate.toEmbeddedCore embedding) circuit

/-- compile後の葉列は、元の葉列へのgate compile mapそのものである。 -/
theorem compileCircuitToCore_flatten
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    (compileCircuitToCore embedding circuit).flatten =
      circuit.flatten.map (PrimitiveGate.toEmbeddedCore embedding) := by
  exact VerifiedCircuitCore.Circuit.flatten_mapGates
    (PrimitiveGate.toEmbeddedCore embedding) circuit

/-- compileは完全展開後のgate数を変えない。 -/
theorem compileCircuitToCore_gateCount
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    (compileCircuitToCore embedding circuit).gateCount = circuit.gateCount := by
  exact VerifiedCircuitCore.Circuit.gateCount_mapGates
    (PrimitiveGate.toEmbeddedCore embedding) circuit

/--
compile後回路の共有core理想作用素は、各Q gateをcompile後の共有作用素で読む意味論と
一般に一致する。これはgate mapから全回路denotationへの無仮定な合成bridgeである。
-/
theorem compileCircuitToCore_denote
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols symbolValue)
        (compileCircuitToCore embedding circuit) =
      circuit.toIdealOperator
        (fun gate => VerifiedCircuitCore.primitiveGateOperatorWithSymbols symbolValue
          (PrimitiveGate.toEmbeddedCore embedding gate)) := by
  exact VerifiedCircuitCore.Circuit.denote_mapGates
    (VerifiedCircuitCore.primitiveGateOperatorWithSymbols symbolValue)
    (PrimitiveGate.toEmbeddedCore embedding) circuit

/-- 統一register向けexport列。共有core gateを実行順に保持する。 -/
def exportCompiledCoreCircuit
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    List (VerifiedCircuitCore.PrimitiveGate totalQubits) :=
  (compileCircuitToCore embedding circuit).flatten

/-- 統一register向けexport列も、元の葉exportへのgate mapで得られる。 -/
theorem exportCompiledCoreCircuit_eq_map
    {ancillaQubits systemQubits totalQubits : Nat}
    (embedding : QWireEmbedding ancillaQubits systemQubits totalQubits)
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    exportCompiledCoreCircuit embedding circuit =
      circuit.flatten.map (PrimitiveGate.toEmbeddedCore embedding) := by
  exact compileCircuitToCore_flatten embedding circuit

/-- 一般Q block encoding正本を任意の統一registerへcompileする公開入口。 -/
def compileUQCircuitToCore {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate totalQubits) :=
  compileCircuitToCore embedding (uqCircuit p)

/-- 一般Q回路のcore compile後gate数は正本gate数と等しい。 -/
theorem compileUQCircuitToCore_gateCount {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits) :
    (compileUQCircuitToCore p embedding).gateCount = (uqCircuit p).gateCount := by
  exact compileCircuitToCore_gateCount embedding (uqCircuit p)

end

end ProbabilityGeneratorQProof
