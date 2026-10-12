import QLean.Circuits.Foundation.Contracts
import QLean.Circuits.Foundation.PrimitiveGateProofs

/-!
# Exact macro components over the normalized PhaseShift primitive

This module deliberately introduces no macro-gate enumeration.  Each named
macro has its own typed specification, primitive-only circuit, independently
defined operator, exact component, and strict operator equality.  In
particular, `GlobalPhase` is not stated modulo global phase: its four-gate
implementation is proved equal to `globalPhaseOperator` as a matrix.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Typed target for the exact `Z = P(π)` macro. -/
structure PhaseShiftZSpec (qubits : Nat) where
  target : Fin qubits

/-- Typed target for the exact `S = P(π / 2)` macro. -/
structure PhaseShiftSSpec (qubits : Nat) where
  target : Fin qubits

/-- Typed target for the exact `S† = P(-π / 2)` macro. -/
structure PhaseShiftSdgSpec (qubits : Nat) where
  target : Fin qubits

/-- Typed target for the exact `T = P(π / 4)` macro. -/
structure PhaseShiftTSpec (qubits : Nat) where
  target : Fin qubits

/-- Typed target for the exact `T† = P(-π / 4)` macro. -/
structure PhaseShiftTdgSpec (qubits : Nat) where
  target : Fin qubits

/-- Typed target for `Rz(θ) = P(θ / 2); X; P(-θ / 2); X`. -/
structure PhaseShiftRzSpec (qubits : Nat) where
  angle : AngleExpr
  target : Fin qubits

/--
Typed target for `GlobalPhase(α) = P(α); X; P(α); X`.

The witness is a `Fin qubits`, so no global-phase macro can be constructed for
a zero-qubit register.  The circuit restores this witness (and every other
wire) exactly, up to the explicitly retained scalar phase.
-/
structure PhaseShiftGlobalPhaseSpec (qubits : Nat) where
  angle : AngleExpr
  witness : Fin qubits

/-- `P(π)` as a primitive-only circuit. -/
def phaseShiftZCircuit {qubits : Nat}
    (spec : PhaseShiftZSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .gate (.phaseShift .pi spec.target)

/-- `P(π / 2)` as a primitive-only circuit. -/
def phaseShiftSCircuit {qubits : Nat}
    (spec : PhaseShiftSSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .gate (.phaseShift (.div .pi (.rational 2 1 (by decide))) spec.target)

/-- `P(-π / 2)` as a primitive-only circuit. -/
def phaseShiftSdgCircuit {qubits : Nat}
    (spec : PhaseShiftSdgSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .gate (.phaseShift (.neg (.div .pi (.rational 2 1 (by decide)))) spec.target)

/-- `P(π / 4)` as a primitive-only circuit. -/
def phaseShiftTCircuit {qubits : Nat}
    (spec : PhaseShiftTSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .gate (.phaseShift (.div .pi (.rational 4 1 (by decide))) spec.target)

/-- `P(-π / 4)` as a primitive-only circuit. -/
def phaseShiftTdgCircuit {qubits : Nat}
    (spec : PhaseShiftTdgSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .gate (.phaseShift (.neg (.div .pi (.rational 4 1 (by decide)))) spec.target)

/-- The source-order primitive circuit for `Rz(θ)`. -/
def phaseShiftRzCircuit {qubits : Nat}
    (spec : PhaseShiftRzSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .seq (.gate (.phaseShift (.div spec.angle (.rational 2 1 (by decide))) spec.target))
    (.seq (.gate (.x spec.target))
      (.seq (.gate (.phaseShift (.neg (.div spec.angle (.rational 2 1 (by decide)))) spec.target))
        (.gate (.x spec.target))))

/-- The source-order primitive circuit for a global phase using one witness wire. -/
def phaseShiftGlobalPhaseCircuit {qubits : Nat}
    (spec : PhaseShiftGlobalPhaseSpec qubits) : Circuit (PrimitiveGate qubits) :=
  .seq (.gate (.phaseShift spec.angle spec.witness))
    (.seq (.gate (.x spec.witness))
      (.seq (.gate (.phaseShift spec.angle spec.witness))
        (.gate (.x spec.witness))))

/-- Independent one-wire phase-shift operator, without a `PrimitiveGate` AST node. -/
def phaseShiftOneWireOperator {qubits : Nat} (angle : ℝ) (target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  embedSingleQubitOperator target (localPhaseShift angle)

/-- Independent Pauli-X operator, specified by its deterministic basis action. -/
def phaseShiftXOperator {qubits : Nat} (target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (xorWire target true)

/-- Independent operator for the `Z = P(π)` macro. -/
def phaseShiftZOperator {qubits : Nat} (_symbolValue : String → ℝ)
    (spec : PhaseShiftZSpec qubits) : Operator (QubitBasis qubits) :=
  phaseShiftOneWireOperator Real.pi spec.target

/-- Independent operator for the `S = P(π / 2)` macro. -/
def phaseShiftSOperator {qubits : Nat} (_symbolValue : String → ℝ)
    (spec : PhaseShiftSSpec qubits) : Operator (QubitBasis qubits) :=
  phaseShiftOneWireOperator (Real.pi / 2) spec.target

/-- Independent operator for the `S† = P(-π / 2)` macro. -/
def phaseShiftSdgOperator {qubits : Nat} (_symbolValue : String → ℝ)
    (spec : PhaseShiftSdgSpec qubits) : Operator (QubitBasis qubits) :=
  phaseShiftOneWireOperator (-(Real.pi / 2)) spec.target

/-- Independent operator for the `T = P(π / 4)` macro. -/
def phaseShiftTOperator {qubits : Nat} (_symbolValue : String → ℝ)
    (spec : PhaseShiftTSpec qubits) : Operator (QubitBasis qubits) :=
  phaseShiftOneWireOperator (Real.pi / 4) spec.target

/-- Independent operator for the `T† = P(-π / 4)` macro. -/
def phaseShiftTdgOperator {qubits : Nat} (_symbolValue : String → ℝ)
    (spec : PhaseShiftTdgSpec qubits) : Operator (QubitBasis qubits) :=
  phaseShiftOneWireOperator (-(Real.pi / 4)) spec.target

/-- The standard, independently specified `Rz` operator. -/
def phaseShiftRzOperator {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftRzSpec qubits) : Operator (QubitBasis qubits) :=
  embedSingleQubitOperator spec.target (localRz (spec.angle.eval symbolValue))

/-- The standard global-phase operator; no projective quotient is used. -/
def phaseShiftGlobalPhaseOperator {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftGlobalPhaseSpec qubits) : Operator (QubitBasis qubits) :=
  globalPhaseOperator (basis := QubitBasis qubits) (spec.angle.eval symbolValue)

/-- The local diagonal presentation used to prove the exact `Rz` identity. -/
def phaseShiftRzLocalOperator (angle : ℝ) : Matrix Bool Bool ℂ :=
  fun output input =>
    if output ≠ input then 0 else if input then
      Complex.exp (Complex.I * ((angle / 2 : ℝ) : ℂ))
    else
      Complex.exp (Complex.I * ((-(angle / 2) : ℝ) : ℂ))

/-- The local diagonal presentation is the standard `Rz` matrix. -/
theorem phaseShiftRzLocalOperator_eq_localRz (angle : ℝ) :
    phaseShiftRzLocalOperator angle = localRz angle := by
  ext output input
  cases output <;> cases input <;>
    simp [phaseShiftRzLocalOperator, localRz]

/-- A phase-shift acts diagonally on each computational-basis ket. -/
theorem phaseShiftOneWireOperator_apply_basisKet
    {qubits : Nat} (angle : ℝ) (target : Fin qubits)
    (input : QubitBasis qubits) :
    applyOperator (phaseShiftOneWireOperator angle target) (basisKet input) =
      (if input target then Complex.exp (Complex.I * (angle : ℂ)) else 1) •
        basisKet input := by
  funext output
  simp only [phaseShiftOneWireOperator]
  rw [applyOperator_basisKet, embedSingleQubitOperator_apply]
  by_cases outputEqual : output = input
  · subst output
    simp [agreesExcept, localPhaseShift, localPhase, basisKet]
  · by_cases outsideEqual : agreesExcept target output input
    · have targetDifferent : output target ≠ input target := by
        intro targetEqual
        apply outputEqual
        funext wire
        by_cases wireEqual : wire = target
        · subst wire
          exact targetEqual
        · exact outsideEqual wire wireEqual
      simp [outsideEqual, localPhaseShift, localPhase, targetDifferent,
        basisKet, outputEqual]
    · simp [outsideEqual, basisKet, outputEqual]

/-- The primitive `X` denotation equals its independent deterministic operator. -/
theorem primitiveXOperator_eq_phaseShiftXOperator
    {qubits : Nat} (symbolValue : String → ℝ) (target : Fin qubits) :
    primitiveGateOperatorWithSymbols symbolValue (.x target) = phaseShiftXOperator target := by
  ext output input
  simp only [primitiveGateOperatorWithSymbols]
  rw [embedSingleQubitOperator_apply]
  by_cases outsideEqual : agreesExcept target output input
  · have outputEqual : output = xorWire target true input ↔
        output target = !input target := by
      constructor
      · intro equal
        subst output
        simp [xorWire]
      · intro targetEqual
        funext wire
        by_cases wireEqual : wire = target
        · subst wire
          simpa [xorWire] using targetEqual
        · calc
            output wire = input wire := outsideEqual wire wireEqual
            _ = xorWire target true input wire :=
              (xorWire_apply_other target wire wireEqual true input).symm
    simp [phaseShiftXOperator, outsideEqual, localX, outputEqual]
  · have outputDifferent : output ≠ xorWire target true input := by
      intro equal
      apply outsideEqual
      intro wire wireDifferent
      rw [equal]
      exact xorWire_apply_other target wire wireDifferent true input
    simp [phaseShiftXOperator, outsideEqual, outputDifferent]

/-- The independent `X` operator acts by the requested one-wire XOR. -/
theorem phaseShiftXOperator_apply_basisKet
    {qubits : Nat} (target : Fin qubits) (input : QubitBasis qubits) :
    applyOperator (phaseShiftXOperator target) (basisKet input) =
      basisKet (xorWire target true input) := by
  exact applyOperator_deterministicOperator_basisKet (xorWire target true) input

/-- Independent source-order operator for the exact `Rz` macro. -/
def phaseShiftRzExpansionOperator {qubits : Nat} (angle : ℝ) (target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  phaseShiftXOperator target *
    (phaseShiftOneWireOperator (-(angle / 2)) target *
      (phaseShiftXOperator target * phaseShiftOneWireOperator (angle / 2) target))

/-- Independent source-order operator for the exact global-phase macro. -/
def phaseShiftGlobalPhaseExpansionOperator {qubits : Nat} (angle : ℝ)
    (witness : Fin qubits) : Operator (QubitBasis qubits) :=
  phaseShiftXOperator witness *
    (phaseShiftOneWireOperator angle witness *
      (phaseShiftXOperator witness * phaseShiftOneWireOperator angle witness))

/-- Basis action of the standard local `Rz` operator. -/
theorem phaseShiftRzOperator_apply_basisKet
    {qubits : Nat} (angle : ℝ) (target : Fin qubits)
    (input : QubitBasis qubits) :
    applyOperator
        (embedSingleQubitOperator target (phaseShiftRzLocalOperator angle))
        (basisKet input) =
      (if input target then
        Complex.exp (Complex.I * ((angle / 2 : ℝ) : ℂ))
      else
        Complex.exp (Complex.I * ((-(angle / 2) : ℝ) : ℂ))) • basisKet input := by
  funext output
  rw [applyOperator_basisKet, embedSingleQubitOperator_apply]
  by_cases outputEqual : output = input
  · subst output
    simp [agreesExcept, phaseShiftRzLocalOperator, basisKet]
  · by_cases outsideEqual : agreesExcept target output input
    · have targetDifferent : output target ≠ input target := by
        intro targetEqual
        apply outputEqual
        funext wire
        by_cases wireEqual : wire = target
        · subst wire
          exact targetEqual
        · exact outsideEqual wire wireEqual
      simp [outsideEqual, phaseShiftRzLocalOperator, targetDifferent,
        basisKet, outputEqual]
    · simp [outsideEqual, basisKet, outputEqual]

/-- The four-gate `P(θ/2); X; P(-θ/2); X` expansion has the exact `Rz` action. -/
theorem phaseShiftRzExpansionOperator_apply_basisKet
    {qubits : Nat} (angle : ℝ) (target : Fin qubits)
    (input : QubitBasis qubits) :
    applyOperator (phaseShiftRzExpansionOperator angle target) (basisKet input) =
      (if input target then
        Complex.exp (Complex.I * ((angle / 2 : ℝ) : ℂ))
      else
        Complex.exp (Complex.I * ((-(angle / 2) : ℝ) : ℂ))) • basisKet input := by
  unfold phaseShiftRzExpansionOperator
  simp only [applyOperator_mul, phaseShiftOneWireOperator_apply_basisKet,
    applyOperator_smul, phaseShiftXOperator_apply_basisKet]
  rw [xorWire_involutive target true input]
  cases inputBit : input target <;>
    simp [inputBit, xorWire_apply_same]

/-- `P(θ/2); X; P(-θ/2); X` is exactly `Rz(θ)`, not merely projectively equal. -/
theorem phaseShiftRzExpansionOperator_eq_Rz
    {qubits : Nat} (angle : ℝ) (target : Fin qubits) :
    phaseShiftRzExpansionOperator angle target =
      embedSingleQubitOperator target (localRz angle) := by
  have localEqual := congrArg (embedSingleQubitOperator target)
    (phaseShiftRzLocalOperator_eq_localRz angle)
  rw [← localEqual]
  ext output input
  calc
    phaseShiftRzExpansionOperator angle target output input =
        applyOperator (phaseShiftRzExpansionOperator angle target) (basisKet input) output := by
          rw [applyOperator_basisKet]
    _ = ((if input target then
        Complex.exp (Complex.I * ((angle / 2 : ℝ) : ℂ))
      else Complex.exp (Complex.I * ((-(angle / 2) : ℝ) : ℂ))) • basisKet input) output := by
          exact congrFun
            (phaseShiftRzExpansionOperator_apply_basisKet angle target input) output
    _ = applyOperator
          (embedSingleQubitOperator target (phaseShiftRzLocalOperator angle))
          (basisKet input) output := by
          exact (congrFun (phaseShiftRzOperator_apply_basisKet angle target input) output).symm
    _ = embedSingleQubitOperator target (phaseShiftRzLocalOperator angle)
          output input := by
          rw [applyOperator_basisKet]

/-- Basis action of the standard global-phase matrix. -/
theorem phaseShiftGlobalPhaseOperator_apply_basisKet
    {qubits : Nat} (angle : ℝ) (input : QubitBasis qubits) :
    applyOperator (globalPhaseOperator (basis := QubitBasis qubits) angle)
        (basisKet input) =
      Complex.exp (Complex.I * (angle : ℂ)) • basisKet input := by
  funext output
  rw [applyOperator_basisKet]
  by_cases outputEqual : output = input
  · subst output
    simp [globalPhaseOperator, basisKet]
  · simp [globalPhaseOperator, basisKet, outputEqual]

/-- The four-gate witness implementation restores every basis wire exactly. -/
theorem phaseShiftGlobalPhaseExpansionOperator_apply_basisKet
    {qubits : Nat} (angle : ℝ) (witness : Fin qubits)
    (input : QubitBasis qubits) :
    applyOperator (phaseShiftGlobalPhaseExpansionOperator angle witness)
        (basisKet input) =
      Complex.exp (Complex.I * (angle : ℂ)) • basisKet input := by
  unfold phaseShiftGlobalPhaseExpansionOperator
  simp only [applyOperator_mul, phaseShiftOneWireOperator_apply_basisKet,
    applyOperator_smul, phaseShiftXOperator_apply_basisKet]
  rw [xorWire_involutive witness true input]
  cases inputBit : input witness <;>
    simp [inputBit, xorWire_apply_same]

/-- The global-phase expansion is strict equality to the full global-phase operator. -/
theorem phaseShiftGlobalPhaseExpansionOperator_eq_globalPhase
    {qubits : Nat} (angle : ℝ) (witness : Fin qubits) :
    phaseShiftGlobalPhaseExpansionOperator angle witness =
      globalPhaseOperator (basis := QubitBasis qubits) angle := by
  ext output input
  calc
    phaseShiftGlobalPhaseExpansionOperator angle witness output input =
        applyOperator (phaseShiftGlobalPhaseExpansionOperator angle witness)
          (basisKet input) output := by
          rw [applyOperator_basisKet]
    _ = (Complex.exp (Complex.I * (angle : ℂ)) • basisKet input) output := by
          exact congrFun
            (phaseShiftGlobalPhaseExpansionOperator_apply_basisKet angle witness input) output
    _ = applyOperator (globalPhaseOperator (basis := QubitBasis qubits) angle)
          (basisKet input) output := by
          exact (congrFun (phaseShiftGlobalPhaseOperator_apply_basisKet angle input) output).symm
    _ = globalPhaseOperator (basis := QubitBasis qubits) angle output input := by
          rw [applyOperator_basisKet]

/-- Strict denotation equality for `Z = P(π)`. -/
theorem phaseShiftZCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : PhaseShiftZSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftZCircuit spec) =
      phaseShiftZOperator symbolValue spec := by
  rfl

/-- Strict denotation equality for `S = P(π / 2)`. -/
theorem phaseShiftSCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : PhaseShiftSSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftSCircuit spec) =
      phaseShiftSOperator symbolValue spec := by
  simp [Circuit.denote, phaseShiftSCircuit, phaseShiftSOperator,
    phaseShiftOneWireOperator, primitiveGateOperatorWithSymbols, AngleExpr.eval]

/-- Strict denotation equality for `S† = P(-π / 2)`. -/
theorem phaseShiftSdgCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : PhaseShiftSdgSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftSdgCircuit spec) =
      phaseShiftSdgOperator symbolValue spec := by
  simp [Circuit.denote, phaseShiftSdgCircuit, phaseShiftSdgOperator,
    phaseShiftOneWireOperator, primitiveGateOperatorWithSymbols, AngleExpr.eval]

/-- Strict denotation equality for `T = P(π / 4)`. -/
theorem phaseShiftTCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : PhaseShiftTSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftTCircuit spec) =
      phaseShiftTOperator symbolValue spec := by
  simp [Circuit.denote, phaseShiftTCircuit, phaseShiftTOperator,
    phaseShiftOneWireOperator, primitiveGateOperatorWithSymbols, AngleExpr.eval]

/-- Strict denotation equality for `T† = P(-π / 4)`. -/
theorem phaseShiftTdgCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : PhaseShiftTdgSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftTdgCircuit spec) =
      phaseShiftTdgOperator symbolValue spec := by
  simp [Circuit.denote, phaseShiftTdgCircuit, phaseShiftTdgOperator,
    phaseShiftOneWireOperator, primitiveGateOperatorWithSymbols, AngleExpr.eval]

/-- Strict denotation equality for the `Rz` macro. -/
theorem phaseShiftRzCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : PhaseShiftRzSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftRzCircuit spec) =
      phaseShiftRzOperator symbolValue spec := by
  rw [Circuit.denote_eq_operatorSequence_flatten]
  unfold phaseShiftRzCircuit
  simp only [Circuit.flatten, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, operatorSequence]
  simp only [one_mul]
  rw [mul_assoc, mul_assoc]
  change
    primitiveGateOperatorWithSymbols symbolValue (.x spec.target) *
      (primitiveGateOperatorWithSymbols symbolValue
          (.phaseShift (.neg (.div spec.angle (.rational 2 1 (by decide)))) spec.target) *
        (primitiveGateOperatorWithSymbols symbolValue (.x spec.target) *
          primitiveGateOperatorWithSymbols symbolValue
            (.phaseShift (.div spec.angle (.rational 2 1 (by decide))) spec.target))) =
      phaseShiftRzOperator symbolValue spec
  rw [primitiveXOperator_eq_phaseShiftXOperator]
  simpa [phaseShiftRzExpansionOperator, phaseShiftRzOperator,
    phaseShiftOneWireOperator,
    primitiveGateOperatorWithSymbols, AngleExpr.eval] using
    (phaseShiftRzExpansionOperator_eq_Rz
      (spec.angle.eval symbolValue) spec.target)

/-- Strict denotation equality for the witness-based `GlobalPhase` macro. -/
theorem phaseShiftGlobalPhaseCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftGlobalPhaseSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (phaseShiftGlobalPhaseCircuit spec) =
      phaseShiftGlobalPhaseOperator symbolValue spec := by
  rw [Circuit.denote_eq_operatorSequence_flatten]
  unfold phaseShiftGlobalPhaseCircuit
  simp only [Circuit.flatten, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, operatorSequence]
  simp only [one_mul]
  rw [mul_assoc, mul_assoc]
  change
    primitiveGateOperatorWithSymbols symbolValue (.x spec.witness) *
      (primitiveGateOperatorWithSymbols symbolValue (.phaseShift spec.angle spec.witness) *
        (primitiveGateOperatorWithSymbols symbolValue (.x spec.witness) *
          primitiveGateOperatorWithSymbols symbolValue
            (.phaseShift spec.angle spec.witness))) =
      phaseShiftGlobalPhaseOperator symbolValue spec
  rw [primitiveXOperator_eq_phaseShiftXOperator]
  exact phaseShiftGlobalPhaseExpansionOperator_eq_globalPhase
    (spec.angle.eval symbolValue) spec.witness

/-- Exact component for `Z = P(π)`. -/
def phaseShiftZExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftZSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftZCircuit spec
  target := phaseShiftZOperator symbolValue spec
  correct := phaseShiftZCircuit_denote_eq symbolValue spec

/-- Exact component for `S = P(π / 2)`. -/
def phaseShiftSExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftSSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftSCircuit spec
  target := phaseShiftSOperator symbolValue spec
  correct := phaseShiftSCircuit_denote_eq symbolValue spec

/-- Exact component for `S† = P(-π / 2)`. -/
def phaseShiftSdgExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftSdgSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftSdgCircuit spec
  target := phaseShiftSdgOperator symbolValue spec
  correct := phaseShiftSdgCircuit_denote_eq symbolValue spec

/-- Exact component for `T = P(π / 4)`. -/
def phaseShiftTExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftTSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftTCircuit spec
  target := phaseShiftTOperator symbolValue spec
  correct := phaseShiftTCircuit_denote_eq symbolValue spec

/-- Exact component for `T† = P(-π / 4)`. -/
def phaseShiftTdgExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftTdgSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftTdgCircuit spec
  target := phaseShiftTdgOperator symbolValue spec
  correct := phaseShiftTdgCircuit_denote_eq symbolValue spec

/-- Exact component for `Rz(θ)`. -/
def phaseShiftRzExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftRzSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftRzCircuit spec
  target := phaseShiftRzOperator symbolValue spec
  correct := phaseShiftRzCircuit_denote_eq symbolValue spec

/-- Exact component for the witness-based global phase. -/
def phaseShiftGlobalPhaseExactComponent {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftGlobalPhaseSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := phaseShiftGlobalPhaseCircuit spec
  target := phaseShiftGlobalPhaseOperator symbolValue spec
  correct := phaseShiftGlobalPhaseCircuit_denote_eq symbolValue spec

/-- The GlobalPhase API is fail-closed for a zero-qubit register. -/
theorem phaseShiftGlobalPhaseSpec_zeroQubits_elim
    (spec : PhaseShiftGlobalPhaseSpec 0) : False :=
  Fin.elim0 spec.witness

/-- Exact basis-state restoration for the witness-based global-phase circuit. -/
theorem phaseShiftGlobalPhaseCircuit_restores_witness
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftGlobalPhaseSpec qubits) (input : QubitBasis qubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (phaseShiftGlobalPhaseCircuit spec))
        (basisKet input) =
      Complex.exp (Complex.I * ((spec.angle.eval symbolValue : ℝ) : ℂ)) •
        basisKet input := by
  rw [phaseShiftGlobalPhaseCircuit_denote_eq]
  exact phaseShiftGlobalPhaseOperator_apply_basisKet
    (spec.angle.eval symbolValue) input

/-- A local audit predicate: all flattened gates use the normalized primitive language. -/
def PhaseShiftMacroUsesOnlyNormalizedPrimitives {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits)) : Prop :=
  ∀ gate, gate ∈ circuit.flatten → IsNormalizedPrimitive gate

theorem phaseShiftZCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftZSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftZCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftZCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

theorem phaseShiftSCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftSSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftSCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftSCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

theorem phaseShiftSdgCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftSdgSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftSdgCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftSdgCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

theorem phaseShiftTCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftTSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftTCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftTCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

theorem phaseShiftTdgCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftTdgSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftTdgCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftTdgCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

theorem phaseShiftRzCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftRzSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftRzCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftRzCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

theorem phaseShiftGlobalPhaseCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : PhaseShiftGlobalPhaseSpec qubits) :
    PhaseShiftMacroUsesOnlyNormalizedPrimitives (phaseShiftGlobalPhaseCircuit spec) := by
  simp [PhaseShiftMacroUsesOnlyNormalizedPrimitives, phaseShiftGlobalPhaseCircuit,
    Circuit.flatten, IsNormalizedPrimitive]

end

end VerifiedCircuitCore
