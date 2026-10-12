import QLean.History.Jennings.PureSpec
import QLean.History.Implementation.HistoryPipelineQbPlusCleanBlock
import QLean.Circuits.Foundation.PrimitiveGateProofs

set_option autoImplicit false

namespace NativeSignalPhase

open JenningsHistory
open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock

noncomputable def basis (n : Nat) (signalBit : Fin 2)
    (data : QubitBasis n) : QubitBasis (blockQubits119 n) :=
  fun wire => if wire = signalWire119 n then signalBit = 1 else blockBasis119 data wire

theorem basis_outside_signal (n : Nat) (signalBit : Fin 2) (data : QubitBasis n)
    (wire : Fin (blockQubits119 n)) (hwire : wire ≠ signalWire119 n) :
    basis n signalBit data wire = blockBasis119 data wire := by
  simp [basis, hwire]

noncomputable def embedding (n : Nat) :
    (Fin 2 × QubitBasis n) ↪ QubitBasis (blockQubits119 n) where
  toFun := fun pair => basis n pair.1 pair.2
  inj' := by
    rintro ⟨leftBit, leftData⟩ ⟨rightBit, rightData⟩ h
    have hdata : leftData = rightData := by
      funext wire
      have hwire := congrFun h (dataWire119 n wire)
      change basis n leftBit leftData (dataWire119 n wire) =
        basis n rightBit rightData (dataWire119 n wire) at hwire
      rw [basis_outside_signal, basis_outside_signal] at hwire
      · simpa only [blockBasis119_data] using hwire
      · exact dataWire119_ne_signalWire119 wire
      · exact dataWire119_ne_signalWire119 wire
    subst rightData
    have hsignal := congrFun h (signalWire119 n)
    fin_cases leftBit <;> fin_cases rightBit <;>
      simp [basis] at hsignal ⊢

end NativeSignalPhase
