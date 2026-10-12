import QLean.Circuits.CommonKernelReflectionCircuit
import QLean.Circuits.FiniteKernelCircuit

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.CheckpointCircuits

open VerifiedCircuitCore ProbabilityGeneratorQProof

/-- CP01: generator block encoding. -/
def generatorCircuit (parameters : GeneratorParameters) :
    VerifiedCircuitCore.Circuit (PrimitiveGate (generatorQubits parameters)) :=
  (ProbabilityGeneratorQProof.uqCircuit parameters).mapGates
    ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore

/-- CP02: history linear-system block encoding. -/
noncomputable def historyCircuit (input : ExecutableInput) :
    VerifiedCircuitCore.Circuit (PrimitiveGate (historyQubits input)) :=
  (buildHistoryCircuit input).specializeSymbols (fun _ => 0)

/-- CP03: the same finite constructor for theoretical and numerical phases. -/
def kernelReflectionCircuit
    {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (input : FiniteKernelCircuit.Input)
    (phaseProvider : VerifiedMath.Quantum.QSP.FinitePhaseProvider AngleType) :
    VerifiedCircuitCore.Circuit (PrimitiveGate (FiniteKernelCircuit.kernelQubits input)) :=
  FiniteKernelCircuit.kernelReflectionCircuit input phaseProvider

/-- CP04 uses the CP03 circuit with the successful-history readout. -/
def successfulHistoryCircuit
    {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (input : FiniteKernelCircuit.Input)
    (phaseProvider : VerifiedMath.Quantum.QSP.FinitePhaseProvider AngleType) :
    VerifiedCircuitCore.Circuit (PrimitiveGate (FiniteKernelCircuit.kernelQubits input)) :=
  kernelReflectionCircuit input phaseProvider

end QLean.Circuits.CheckpointCircuits

