import QLean.Circuits.FiniteScientificPreparationBridge
import QLean.Circuits.CP03ProgramConversion

/-! Staged common-preparer CP03 entry.  The logical scientific source is
unchanged; the physical register uses the finite emitter's canonical layout.
The final public alias is rebound only together with its dependent readouts. -/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.CommonKernelReflection

open VerifiedCircuitCore M13bPrimitiveCandidate
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open QLean.Circuits.CheckpointCircuits QLean.Circuits.FiniteScientificPreparationBridge
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18

noncomputable section

def canonicalCircuitInput (input : ExecutableInput) : ExecutableInput :=
  { input with circuitSource := (theoreticalCanonicalP18CircuitSource
      input.source input.domain input.fits input.assumptions) }

abbrev commonKernelReflectionQubits (input : ExecutableInput) : Nat :=
  kernelReflectionQubits (canonicalCircuitInput input)

/-- This circuit actually contains the common RHS preparer; it is not a
wrapper around the legacy preparation or a selected target operator. -/
def commonKernelReflectionProgramCircuit
    (input : ExecutableInput) (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate (commonKernelReflectionQubits input)) :=
  ((theoreticalCommonOuterPlan input.source input.domain input.fits input.assumptions).compile
    program .pi).closeSymbolsPreserving (fun _ => 0)

attribute [irreducible] commonKernelReflectionProgramCircuit

end
end QLean.Circuits.CommonKernelReflection
