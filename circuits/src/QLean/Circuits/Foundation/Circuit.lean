import QLean.Circuits.Foundation.Foundations

/-!
# 回路構文木と理想作用素意味論

回路はidentity、単一gate、二項seq、repeatだけからなる。wire写像と制御化は
gate葉を変換する構文操作として定義する。
-/

namespace VerifiedCircuitCore

noncomputable section

open Matrix

/-- gate型に依存しない回路構文木。 -/
inductive Circuit (Gate : Type*) where
  /-- 何もしない空回路。 -/
  | identity
  /-- gate一個だけからなる葉。 -/
  | gate (value : Gate)
  /-- `first`の後に`second`を実行する二項逐次合成。 -/
  | seq (first second : Circuit Gate)
  /-- 同じbodyを指定回数だけ実行する構文node。 -/
  | repeat (count : Nat) (body : Circuit Gate)
deriving Repr

namespace Circuit

/-- 回路を実行順のgate葉リストへ完全展開する。 -/
def flatten {Gate : Type*} : Circuit Gate → List Gate
  | .identity => []
  | .gate value => [value]
  | .seq first second => flatten first ++ flatten second
  | .repeat count body => (List.replicate count (flatten body)).flatten

/-- 完全展開後のgate葉数。 -/
def gateCount {Gate : Type*} (circuit : Circuit Gate) : Nat :=
  circuit.flatten.length

/-- gateの有限列を実行順の回路構文木へ変換する。 -/
def fromList {Gate : Type*} : List Gate → Circuit Gate
  | [] => .identity
  | first :: rest => .seq (.gate first) (fromList rest)

/-- 回路の有限列を実行順に逐次合成する。 -/
def sequence {Gate : Type*} : List (Circuit Gate) → Circuit Gate
  | [] => .identity
  | first :: rest => .seq first (sequence rest)

/-- gate列を回路化して完全展開すると元のgate列へ戻る。 -/
@[simp] theorem flatten_fromList {Gate : Type*} (gates : List Gate) :
    (fromList gates).flatten = gates := by
  induction gates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [fromList, flatten, inductionHypothesis]

/-- 回路列の逐次合成を展開すると、各子回路の展開列の連結になる。 -/
theorem flatten_sequence {Gate : Type*} :
    ∀ circuits : List (Circuit Gate),
      (sequence circuits).flatten = circuits.flatMap flatten
  | [] => by simp [sequence, flatten]
  | first :: rest => by
      simp [sequence, flatten, flatten_sequence rest]

/-- Sequencing singleton gate circuits preserves the original gate list. -/
@[simp] theorem flatten_sequence_map_gate {Gate : Type*} (gates : List Gate) :
    (sequence (gates.map gate)).flatten = gates := by
  rw [flatten_sequence]
  induction gates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [inductionHypothesis, flatten]

/-- gate列から作った回路のgate数は元のlist長である。 -/
@[simp] theorem gateCount_fromList {Gate : Type*} (gates : List Gate) :
    (fromList gates).gateCount = gates.length := by
  simp [gateCount]

/-- 全gate葉へ同じ型付き写像を適用する。 -/
def mapGates {Gate MappedGate : Type*} (mapGate : Gate → MappedGate) :
    Circuit Gate → Circuit MappedGate
  | .identity => .identity
  | .gate value => .gate (mapGate value)
  | .seq first second => .seq (mapGates mapGate first) (mapGates mapGate second)
  | .repeat count body => .repeat count (mapGates mapGate body)

/-- 一つのsource gateを任意のtarget回路へ展開する一般回路compiler。 -/
def compileGates {Gate MappedGate : Type*}
    (compileGate : Gate → Circuit MappedGate) :
    Circuit Gate → Circuit MappedGate
  | .identity => .identity
  | .gate value => compileGate value
  | .seq first second =>
      .seq (compileGates compileGate first) (compileGates compileGate second)
  | .repeat count body => .repeat count (compileGates compileGate body)

/-- 回路compilerの完全展開列は、各source葉のcompiler展開列の連結である。 -/
theorem flatten_compileGates
    {Gate MappedGate : Type*} (compileGate : Gate → Circuit MappedGate) :
    ∀ circuit : Circuit Gate,
      (circuit.compileGates compileGate).flatten =
        circuit.flatten.flatMap (fun gate => (compileGate gate).flatten)
  | .identity => rfl
  | .gate _ => by simp [compileGates, flatten]
  | .seq first second => by
      simp [compileGates, flatten, flatten_compileGates compileGate first,
        flatten_compileGates compileGate second]
  | .repeat count body => by
      simp only [compileGates, flatten,
        flatten_compileGates compileGate body]
      induction count with
      | zero => rfl
      | succ count inductionHypothesis =>
          simp [List.replicate_succ, inductionHypothesis,
            List.flatMap_append]

/-- gate列回路へのgate写像は、list写像後のgate列回路と一致する。 -/
theorem mapGates_fromList
    {Gate MappedGate : Type*} (mapGate : Gate → MappedGate) :
    ∀ gates : List Gate,
      (fromList gates).mapGates mapGate = fromList (gates.map mapGate)
  | [] => rfl
  | first :: rest => by
      simp [fromList, mapGates, mapGates_fromList mapGate rest]

/-- 回路列へのgate写像は、各子回路への写像後の逐次合成と一致する。 -/
theorem mapGates_sequence
    {Gate MappedGate : Type*} (mapGate : Gate → MappedGate) :
    ∀ circuits : List (Circuit Gate),
      (sequence circuits).mapGates mapGate =
        sequence (circuits.map (mapGates mapGate))
  | [] => rfl
  | first :: rest => by
      simp [sequence, mapGates, mapGates_sequence mapGate rest]

/-- 二回のgate写像は合成した一回のgate写像へまとめられる。 -/
theorem mapGates_mapGates
    {Gate MiddleGate MappedGate : Type*}
    (first : Gate → MiddleGate) (second : MiddleGate → MappedGate) :
    ∀ circuit : Circuit Gate,
      (circuit.mapGates first).mapGates second =
        circuit.mapGates (second ∘ first)
  | .identity => rfl
  | .gate _ => rfl
  | .seq left right => by
      simp [mapGates, mapGates_mapGates first second left,
        mapGates_mapGates first second right]
  | .repeat count body => by
      simp [mapGates, mapGates_mapGates first second body]

/-- Mapping every gate by the identity function preserves the circuit AST. -/
@[simp] theorem mapGates_id {Gate : Type*} (circuit : Circuit Gate) :
    circuit.mapGates id = circuit := by
  induction circuit with
  | identity => rfl
  | gate value => rfl
  | seq first second firstInduction secondInduction =>
      simp [mapGates, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp [mapGates, inductionHypothesis]

/-- gate写像後の完全展開列は、元の展開列へのlist mapである。 -/
theorem flatten_mapGates
    {Gate MappedGate : Type*} (mapGate : Gate → MappedGate) :
    ∀ circuit : Circuit Gate,
      (circuit.mapGates mapGate).flatten = circuit.flatten.map mapGate
  | .identity => rfl
  | .gate _ => rfl
  | .seq first second => by
      simp [flatten, mapGates, flatten_mapGates mapGate first,
        flatten_mapGates mapGate second]
  | .repeat count body => by
      simp [flatten, mapGates, flatten_mapGates mapGate body,
        List.map_flatten]

/-- gate写像は完全展開後のgate数を変えない。 -/
theorem gateCount_mapGates
    {Gate MappedGate : Type*} (mapGate : Gate → MappedGate)
    (circuit : Circuit Gate) :
    (circuit.mapGates mapGate).gateCount = circuit.gateCount := by
  simp [gateCount, flatten_mapGates]

/-- wire写像をgate写像として回路全体へ適用する。 -/
def mapWires {Gate MappedGate WireMap : Type*}
    (liftGate : WireMap → Gate → MappedGate)
    (wireMap : WireMap) (circuit : Circuit Gate) : Circuit MappedGate :=
  circuit.mapGates (liftGate wireMap)

/-- control情報をgate葉へ付加して制御回路を作る。 -/
def control {Gate ControlledGate Control : Type*}
    (controlGate : Control → Gate → ControlledGate)
    (control : Control) (circuit : Circuit Gate) : Circuit ControlledGate :=
  circuit.mapGates (controlGate control)

/-- 各gateを逆gateへ置換し、実行順も反転した逆回路を作る。 -/
def reverse {Gate : Type*} (inverseGate : Gate → Gate) : Circuit Gate → Circuit Gate
  | .identity => .identity
  | .gate value => .gate (inverseGate value)
  | .seq first second => .seq (reverse inverseGate second) (reverse inverseGate first)
  | .repeat count body => .repeat count (reverse inverseGate body)

/-- compute、use、computeの逆実行を一個の構文木へまとめる。 -/
def computeUseUncompute {Gate : Type*} (inverseGate : Gate → Gate)
    (compute use : Circuit Gate) : Circuit Gate :=
  .seq compute (.seq use (compute.reverse inverseGate))

/-- gate作用素を使って回路構文木を理想作用素へ解釈する。 -/
def denote {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) : Circuit Gate → Operator basis
  | .identity => 1
  | .gate value => gateOperator value
  | .seq first second => denote gateOperator second * denote gateOperator first
  | .repeat count body => (denote gateOperator body) ^ count

/-- `fromList` の denotation は gate 作用素を実行順に掛けた `operatorSequence` である。 -/
theorem denote_fromList_eq_operatorSequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) : ∀ gates : List Gate,
    denote gateOperator (fromList gates) =
      operatorSequence (gates.map gateOperator)
  | [] => rfl
  | first :: rest => by
      simp [fromList, denote, operatorSequence,
        denote_fromList_eq_operatorSequence gateOperator rest]

/-- `sequence` の denotation は子回路の denotation の実行順積である。 -/
theorem denote_sequence_eq_operatorSequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) : ∀ circuits : List (Circuit Gate),
    denote gateOperator (sequence circuits) =
      operatorSequence (circuits.map (denote gateOperator))
  | [] => rfl
  | first :: rest => by
      simp [sequence, denote, operatorSequence,
        denote_sequence_eq_operatorSequence gateOperator rest]

private theorem operatorSequence_flatten_replicate
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (gates : List Gate) :
    ∀ count : Nat,
      operatorSequence (((List.replicate count gates).flatten).map gateOperator) =
        operatorSequence (gates.map gateOperator) ^ count
  | 0 => rfl
  | count + 1 => by
      change operatorSequence
          ((gates ++ (List.replicate count gates).flatten).map gateOperator) =
        operatorSequence (gates.map gateOperator) ^ (count + 1)
      rw [List.map_append, operatorSequence_append,
        operatorSequence_flatten_replicate gateOperator gates count, pow_succ]

/-- A circuit denotation depends only on its execution-order flat gate list. -/
theorem denote_eq_operatorSequence_flatten
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) : ∀ circuit : Circuit Gate,
    denote gateOperator circuit =
      operatorSequence (circuit.flatten.map gateOperator)
  | .identity => rfl
  | .gate value => by simp [denote, flatten, operatorSequence]
  | .seq first second => by
      change denote gateOperator second * denote gateOperator first = _
      rw [denote_eq_operatorSequence_flatten gateOperator first,
        denote_eq_operatorSequence_flatten gateOperator second]
      simp [flatten, operatorSequence_append]
  | .repeat count body => by
      change (denote gateOperator body) ^ count = _
      rw [denote_eq_operatorSequence_flatten gateOperator body]
      exact (operatorSequence_flatten_replicate
        gateOperator body.flatten count).symm

/-- Circuits with the same flat gate stream have the same denotation. -/
theorem denote_eq_of_flatten
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (first second : Circuit Gate)
    (flatten_eq : first.flatten = second.flatten) :
    denote gateOperator first = denote gateOperator second := by
  rw [denote_eq_operatorSequence_flatten,
    denote_eq_operatorSequence_flatten, flatten_eq]

/-- 子回路ごとの解析 target 等式から、`sequence (map ...)` 全体の作用素積等式を得る。 -/
theorem denote_sequence_map_eq_operatorSequence
    {Item Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (circuitOf : Item → Circuit Gate) (targetOf : Item → Operator basis)
    (correct : ∀ item, denote gateOperator (circuitOf item) = targetOf item) :
    ∀ items : List Item,
      denote gateOperator (sequence (items.map circuitOf)) =
        operatorSequence (items.map targetOf)
  | [] => rfl
  | first :: rest => by
      simp [sequence, denote, operatorSequence, correct first,
        denote_sequence_map_eq_operatorSequence gateOperator circuitOf targetOf
          correct rest]

/-- 二項seqの意味論は実行順に対応する行列積である。 -/
@[simp] theorem denote_seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (first second : Circuit Gate) :
    denote gateOperator (.seq first second) =
      denote gateOperator second * denote gateOperator first := rfl

/-- repeat nodeの意味論はbody作用素の自然数冪である。 -/
@[simp] theorem denote_repeat
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (count : Nat) (body : Circuit Gate) :
    denote gateOperator (.repeat count body) = (denote gateOperator body) ^ count := rfl

/-- 全基本gateがunitaryなら、構文木から合成した全回路もunitaryである。 -/
theorem denote_mem_unitaryGroup
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gateUnitary : ∀ value, gateOperator value ∈ Matrix.unitaryGroup basis ℂ) :
    ∀ circuit : Circuit Gate,
      circuit.denote gateOperator ∈ Matrix.unitaryGroup basis ℂ
  | .identity => Submonoid.one_mem _
  | .gate value => gateUnitary value
  | .seq first second =>
      Submonoid.mul_mem _
        (denote_mem_unitaryGroup gateOperator gateUnitary second)
        (denote_mem_unitaryGroup gateOperator gateUnitary first)
  | .repeat count body =>
      Submonoid.pow_mem _
        (denote_mem_unitaryGroup gateOperator gateUnitary body) count

/-- gate意味論が各葉で一致すれば、回路全体の理想作用素も一致する。 -/
theorem denote_congr
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {left right : Gate → Operator basis}
    (equal : ∀ gate, left gate = right gate) :
    ∀ circuit : Circuit Gate, denote left circuit = denote right circuit
  | .identity => rfl
  | .gate value => equal value
  | .seq first second => by
      rw [denote_seq, denote_seq, denote_congr equal first, denote_congr equal second]
  | .repeat count body => by
      rw [denote_repeat, denote_repeat, denote_congr equal body]

/-- map後回路の意味論は、mapをgate意味論へ前合成した意味論に等しい。 -/
theorem denote_mapGates
    {Gate MappedGate basis : Type*} [Fintype basis] [DecidableEq basis]
    (mappedOperator : MappedGate → Operator basis) (mapGate : Gate → MappedGate) :
    ∀ circuit : Circuit Gate,
      denote mappedOperator (circuit.mapGates mapGate) =
        denote (mappedOperator ∘ mapGate) circuit
  | .identity => rfl
  | .gate _ => rfl
  | .seq first second => by
      simp only [mapGates, denote_seq, denote_mapGates mappedOperator mapGate first,
        denote_mapGates mappedOperator mapGate second]
  | .repeat count body => by
      simp only [mapGates, denote_repeat, denote_mapGates mappedOperator mapGate body]

/-- 各逆gateが共役転置を表すなら、逆回路全体も共役転置を表す。 -/
theorem denote_reverse
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (inverseGate : Gate → Gate) (gateOperator : Gate → Operator basis)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = (gateOperator gate)ᴴ) :
    ∀ circuit : Circuit Gate,
      denote gateOperator (circuit.reverse inverseGate) =
        (denote gateOperator circuit)ᴴ
  | .identity => by simp [reverse, denote]
  | .gate value => inverseCorrect value
  | .seq first second => by
      simp only [reverse, denote_seq, denote_reverse inverseGate gateOperator
        inverseCorrect first, denote_reverse inverseGate gateOperator inverseCorrect second,
        Matrix.conjTranspose_mul]
  | .repeat count body => by
      simp only [reverse, denote_repeat,
        denote_reverse inverseGate gateOperator inverseCorrect body]
      let operator := denote gateOperator body
      change (operatorᴴ) ^ count = (operator ^ count)ᴴ
      induction count with
      | zero => simp
      | succ count inductionHypothesis =>
          calc
            (operatorᴴ) ^ (count + 1) = (operatorᴴ) ^ count * operatorᴴ := pow_succ _ _
            _ = (operator ^ count)ᴴ * operatorᴴ := by rw [inductionHypothesis]
            _ = (operator * operator ^ count)ᴴ := by rw [Matrix.conjTranspose_mul]
            _ = (operator ^ (count + 1))ᴴ := by rw [pow_succ']

/-- control作用素がidentity・積・gate葉を保てば、制御化は全回路で意味を保つ。 -/
structure ControlSemantics
    {Gate ControlledGate Control basis : Type*}
    [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (controlledGateOperator : ControlledGate → Operator basis)
    (controlGate : Control → Gate → ControlledGate)
    (controlOperator : Control → Operator basis → Operator basis) where
  /-- 制御化はidentity作用素を保存する。 -/
  identity : ∀ control, controlOperator control 1 = 1
  /-- 制御化は実行順の作用素積を保存する。 -/
  multiplication : ∀ control second first,
    controlOperator control (second * first) =
      controlOperator control second * controlOperator control first
  /-- gate一葉の制御化は指定した制御作用素に一致する。 -/
  gate : ∀ control value,
    controlledGateOperator (controlGate control value) =
      controlOperator control (gateOperator value)

/-- `ControlSemantics`を満たす制御化は回路全体の制御作用素に一致する。 -/
theorem denote_control
    {Gate ControlledGate Control basis : Type*}
    [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (controlledGateOperator : ControlledGate → Operator basis)
    (controlGate : Control → Gate → ControlledGate)
    (controlOperator : Control → Operator basis → Operator basis)
    (laws : ControlSemantics gateOperator controlledGateOperator controlGate controlOperator)
    (control : Control) : ∀ circuit : Circuit Gate,
      denote controlledGateOperator (circuit.control controlGate control) =
        controlOperator control (denote gateOperator circuit)
  | .identity => (laws.identity control).symm
  | .gate value => laws.gate control value
  | .seq first second => by
      change
        denote controlledGateOperator (second.mapGates (controlGate control)) *
            denote controlledGateOperator (first.mapGates (controlGate control)) =
          controlOperator control
            (denote gateOperator second * denote gateOperator first)
      have secondEqual :
          denote controlledGateOperator (second.mapGates (controlGate control)) =
            controlOperator control (denote gateOperator second) := by
        simpa [Circuit.control] using
          denote_control gateOperator controlledGateOperator controlGate
            controlOperator laws control second
      have firstEqual :
          denote controlledGateOperator (first.mapGates (controlGate control)) =
            controlOperator control (denote gateOperator first) := by
        simpa [Circuit.control] using
          denote_control gateOperator controlledGateOperator controlGate
            controlOperator laws control first
      rw [secondEqual, firstEqual]
      exact (laws.multiplication control _ _).symm
  | .repeat count body => by
      change
        (denote controlledGateOperator (body.mapGates (controlGate control))) ^ count =
          controlOperator control ((denote gateOperator body) ^ count)
      induction count with
      | zero => simpa using (laws.identity control).symm
      | succ count inductionHypothesis =>
          rw [pow_succ, pow_succ]
          rw [inductionHypothesis]
          have bodyEqual :
              denote controlledGateOperator (body.mapGates (controlGate control)) =
                controlOperator control (denote gateOperator body) := by
            simpa [Circuit.control] using
              denote_control gateOperator controlledGateOperator controlGate
                controlOperator laws control body
          rw [bodyEqual]
          exact (laws.multiplication control _ _).symm

end Circuit

end

end VerifiedCircuitCore
