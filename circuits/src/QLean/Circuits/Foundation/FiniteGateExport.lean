import QLean.Circuits.Foundation.Gates

/-! Proof-free, executable serialization of a finite primitive circuit.
`none` rejects an unresolved symbol or an opaque real constant instead of
quietly substituting an arbitrary numerical value. -/

set_option autoImplicit false

namespace VerifiedCircuitCore

inductive FiniteAngle where
  | rational (numerator : Int) (denominator : Nat)
  | decimal (mantissa : Int) (scale : Nat)
  | pi
  | add (left right : FiniteAngle)
  | mul (left right : FiniteAngle)
  | div (left right : FiniteAngle)
  | neg (value : FiniteAngle)
  | sqrt (value : FiniteAngle)
  | acos (value : FiniteAngle)
  deriving Repr, DecidableEq

/-- A compact single-line syntax for exported exact angles. -/
def FiniteAngle.serialize : FiniteAngle → String
  | .rational numerator denominator => s!"rat({numerator},{denominator})"
  | .decimal mantissa scale => s!"dec({mantissa},{scale})"
  | .pi => "pi"
  | .add left right => s!"add({left.serialize},{right.serialize})"
  | .mul left right => s!"mul({left.serialize},{right.serialize})"
  | .div left right => s!"div({left.serialize},{right.serialize})"
  | .neg value => s!"neg({value.serialize})"
  | .sqrt value => s!"sqrt({value.serialize})"
  | .acos value => s!"acos({value.serialize})"

def AngleExpr.toFinite? : AngleExpr → Option FiniteAngle
  | .const _ => none
  | .symbol _ => none
  | .rational numerator denominator _ => some (.rational numerator denominator)
  | .decimal mantissa scale => some (.decimal mantissa scale)
  | .pi => some .pi
  | .add left right => do
      let left ← left.toFinite?
      let right ← right.toFinite?
      return .add left right
  | .mul left right => do
      let left ← left.toFinite?
      let right ← right.toFinite?
      return .mul left right
  | .div left right => do
      let left ← left.toFinite?
      let right ← right.toFinite?
      return .div left right
  | .neg value => do
      let value ← value.toFinite?
      return .neg value
  | .sqrt value => do
      let value ← value.toFinite?
      return .sqrt value
  | .acos value => do
      let value ← value.toFinite?
      return .acos value

structure FiniteGate where
  kind : String
  wires : List Nat
  angle : Option FiniteAngle := none
  deriving Repr, DecidableEq

def FiniteGate.tsvLine (gate : FiniteGate) : String :=
  let wires := String.intercalate "," (gate.wires.map toString)
  let angle := gate.angle.map FiniteAngle.serialize |>.getD ""
  s!"{gate.kind}\t{wires}\t{angle}"

def PrimitiveGate.toFinite? {qubits : Nat} :
    PrimitiveGate qubits → Option FiniteGate
  | .x target => some ⟨"X", [target.val], none⟩
  | .h target => some ⟨"H", [target.val], none⟩
  | .ry angle target => do
      let angle ← angle.toFinite?
      return ⟨"Ry", [target.val], some angle⟩
  | .phaseShift angle target => do
      let angle ← angle.toFinite?
      return ⟨"Phase", [target.val], some angle⟩
  | .cnot control target _ =>
      some ⟨"CNOT", [control.val, target.val], none⟩
  | .toffoli first second target _ _ _ =>
      some ⟨"Toffoli", [first.val, second.val, target.val], none⟩

def Circuit.toFiniteGates? {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits)) : Option (List FiniteGate) :=
  circuit.flatten.mapM PrimitiveGate.toFinite?

/-- A work-stack traversal of the same circuit syntax.  It emits gates in
`flatten` order without materializing repeated intermediate concatenations.
This is an exporter only; it attaches no semantic certificate to the output. -/
private inductive PendingFiniteCircuit (qubits : Nat) where
  | circuit : Circuit (PrimitiveGate qubits) → PendingFiniteCircuit qubits
  | repeated : Nat → Circuit (PrimitiveGate qubits) → PendingFiniteCircuit qubits

private partial def emitFiniteGatesFast?
    {qubits : Nat} (pending : List (PendingFiniteCircuit qubits))
    (reversed : List FiniteGate) : Option (List FiniteGate) :=
  match pending with
  | [] => some reversed.reverse
  | .circuit .identity :: rest => emitFiniteGatesFast? rest reversed
  | .circuit (.gate gate) :: rest =>
      match gate.toFinite? with
      | none => none
      | some finiteGate => emitFiniteGatesFast? rest (finiteGate :: reversed)
  | .circuit (.seq first second) :: rest =>
      emitFiniteGatesFast? (.circuit first :: .circuit second :: rest) reversed
  | .circuit (.repeat count body) :: rest =>
      emitFiniteGatesFast? (.repeated count body :: rest) reversed
  | .repeated 0 _ :: rest => emitFiniteGatesFast? rest reversed
  | .repeated (count + 1) body :: rest =>
      emitFiniteGatesFast? (.circuit body :: .repeated count body :: rest) reversed

def Circuit.toFiniteGatesFast? {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits)) : Option (List FiniteGate) :=
  emitFiniteGatesFast? [.circuit circuit] []

end VerifiedCircuitCore
