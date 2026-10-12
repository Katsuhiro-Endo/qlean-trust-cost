import QLean.SignalProcessing.M13bChebyshevCoordinateBridge
import QLean.Circuits.Foundation.ControlledCircuitCompiler

/-!
# M13b: exact external-control lift of the selected compute word

Unlike a merely syntactic controlled circuit, the legacy verified compiler
provides an independent clean-work semantic target: the controlled wire lift
of the source operator.  This module instantiates that result for the actual
KernelQSP primitive compute word.  No caller supplies an operator equality.
-/

set_option autoImplicit false

namespace M13bExternallyControlledCompute

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness

noncomputable section

/-- A standard three-wire external-control extension: one positive control
and the two clean work wires required by the verified leaf compiler. -/
def m13bExternalControlLayout (n : Nat) :
    ExternallyControlledCircuitLayout n (n + 3) :=
  { placement :=
      { toFun := fun source => ⟨source.1, by omega⟩
        inj' := by
          intro left right equal
          apply Fin.ext
          exact congrArg (fun value : Fin (n + 3) => value.val) equal }
    control := ⟨n, by omega⟩
    control_ne_placed := by
      intro source equal
      have values : n = source.1 :=
        congrArg (fun value : Fin (n + 3) => value.val) equal
      omega
    controlWork := [⟨n + 1, by omega⟩, ⟨n + 2, by omega⟩] }

/-- The advertised two compiler work wires are disjoint from control and
the placed source register. -/
def m13bExternalControlCleanWorkValid (n : Nat) :
    (m13bExternalControlLayout n).CleanWorkValid :=
  { work₀ := ⟨n + 1, by omega⟩
    work₁ := ⟨n + 2, by omega⟩
    controlWork_eq := rfl
    work₀_ne_control := by
      intro equal
      have values : n + 1 = n := congrArg Fin.val equal
      omega
    work₁_ne_control := by
      intro equal
      have values : n + 2 = n := congrArg Fin.val equal
      omega
    work₀_ne_work₁ := by
      intro equal
      have values : n + 1 = n + 2 := congrArg Fin.val equal
      omega
    work₀_ne_placed := by
      intro source equal
      have values : n + 1 = source.1 := congrArg Fin.val equal
      omega
    work₁_ne_placed := by
      intro source equal
      have values : n + 2 = source.1 := congrArg Fin.val equal
      omega }

/-- Each closed primitive syntax leaf is accepted by the legacy exact
external-control decoder. -/
theorem primitiveGate_externally_controllable {n : Nat}
    (gate : PrimitiveGate n) : IsExternallyControllablePrimitive gate := by
  cases gate <;> simp [IsExternallyControllablePrimitive]

/-- Values assigned to the three outside wires of the controlled compute
embedding: the selection control is explicit and both compiler work wires are
clean. -/
def m13bControlOutside (n : Nat) (controlValue : Bool) :
    OutsideWire (m13bExternalControlLayout n).placement → Bool :=
  fun wire => if wire.1 = (m13bExternalControlLayout n).control then
    controlValue else false

/-- Embed a source basis label into the controlled register with a selected
control value and clean compiler work wires. -/
def m13bControlledBasis (n : Nat) (controlValue : Bool)
    (input : QubitBasis n) : QubitBasis (n + 3) :=
  fixedOutsideBasisEmbedding (m13bExternalControlLayout n).placement
    (m13bControlOutside n controlValue) input

theorem m13bControlledBasis_control
    (n : Nat) (controlValue : Bool) (input : QubitBasis n) :
    m13bControlledBasis n controlValue input
      (m13bExternalControlLayout n).control = controlValue := by
  classical
  let layout := m13bExternalControlLayout n
  have houtside : ¬ ∃ source, layout.placement source = layout.control := by
    intro existsSource
    rcases existsSource with ⟨source, equal⟩
    exact layout.control_ne_placed source equal.symm
  simp [m13bControlledBasis, m13bControlOutside,
    fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, layout, houtside]

theorem m13bControlledBasis_work_clean
    (n : Nat) (controlValue : Bool) (input : QubitBasis n) :
    externallyControlledCleanWorkPredicate
      (m13bExternalControlCleanWorkValid n)
      (m13bControlledBasis n controlValue input) := by
  constructor
  · classical
    let layout := m13bExternalControlLayout n
    let valid := m13bExternalControlCleanWorkValid n
    have houtside : ¬ ∃ source, layout.placement source = valid.work₀ := by
      intro existsSource
      rcases existsSource with ⟨source, equal⟩
      exact valid.work₀_ne_placed source equal.symm
    have hcontrol : valid.work₀ ≠ layout.control := valid.work₀_ne_control
    simp [m13bControlledBasis, m13bControlOutside,
      fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, layout, valid,
      houtside, hcontrol]
  · classical
    let layout := m13bExternalControlLayout n
    let valid := m13bExternalControlCleanWorkValid n
    have houtside : ¬ ∃ source, layout.placement source = valid.work₁ := by
      intro existsSource
      rcases existsSource with ⟨source, equal⟩
      exact valid.work₁_ne_placed source equal.symm
    have hcontrol : valid.work₁ ≠ layout.control := valid.work₁_ne_control
    simp [m13bControlledBasis, m13bControlOutside,
      fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, layout, valid,
      houtside, hcontrol]

/-- A local Hadamard on the external selection control preserves the same
clean subspace. -/
noncomputable def m13bCleanControlHComponent
    (symbolValue : String → ℝ) (n : Nat) :
    SubspaceMapComponent (primitiveGateOperatorWithSymbols (qubits := n + 3) symbolValue) :=
  let layout := m13bExternalControlLayout n
  let valid := m13bExternalControlCleanWorkValid n
  let clean := externallyControlledCleanWorkPredicate valid
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := n + 3) symbolValue)
    (.gate (.h layout.control))
    (primitiveGateOperatorWithSymbols symbolValue (.h layout.control)) clean clean
    (by
      intro _input _inside
      rfl)
    (by
      intro input inside
      change applyOperator (embedSingleQubitOperator layout.control localH)
        (basisKet input) ∈ SubspaceMapComponent.basisSpan clean
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (embedSingleQubitOperator layout.control localH) {layout.control}
        (OperatorPreservesOutside.embedSingleQubitOperator layout.control localH)
        clean clean
      · intro original output originalClean sameOutside
        constructor
        · rw [sameOutside valid.work₀ (by
            intro member
            apply valid.work₀_ne_control
            simpa using member)]
          exact originalClean.1
        · rw [sameOutside valid.work₁ (by
            intro member
            apply valid.work₁_ne_control
            simpa using member)]
          exact originalClean.2
      · exact inside)

end

end M13bExternallyControlledCompute
