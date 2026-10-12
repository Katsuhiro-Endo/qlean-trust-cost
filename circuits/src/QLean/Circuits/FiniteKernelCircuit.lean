import QLean.Circuits.FiniteScientificCircuitSource
import QLean.Circuits.FiniteKernelPolynomial

/-!
# Finite-input CP03 construction

The provider receives the finite request, not a real polynomial computed by
the caller of the provider. The default provider interprets this request in
the proof layer. An external provider can simply return its supplied word.
Neither the builder nor the request contains a target operator, a phase
certificate, or a chosen FPAA depth.

The public CP03/04/05/08 entries all consume this constructor. Arbitrary-real
input conversion is external; it does not select a separate circuit builder.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteKernelCircuit

open VerifiedCircuitCore
open ExecutableHistoryHistoryEmbedding
open QLean.Circuits.FiniteScientificCircuitSource
open QLean.Circuits.CheckpointCircuits

/-- Finite execution data. The propositions validate scalar bounds and wire
capacity; they contain no phase word or circuit-correctness assumption. -/
structure Input where
  source : FiniteScientificSource
  fits : HistoryIndexFitsLayout119 source.layoutSource
  epsilon : ℚ
  epsilon_pos : 0 < epsilon
  epsilon_lt_two : epsilon < 2

/-- Computable polynomial syntax and degree. Mathematical interpretation is
not executed when an external provider generates finite angles. -/
def Input.polynomialRequest (input : Input) : VerifiedMath.Quantum.QSP.FinitePolynomialRequest :=
  FiniteKernelPolynomial.request input.source.historyParameters.taylorOrder
    input.source.historyParameters.clockEnd input.source.historyParameters.binaryLabels
    input.epsilon input.epsilon_pos input.epsilon_lt_two

abbrev kernelQubits (input : Input) : Nat := input.source.phaseQubits + 3

/-- The same ordinary `def` is used for the existence-based provider and for
finite external phases. Real interpretation happens only inside a provider
that elects to use it. The outer reflection is the finite `.pi` expression. -/
def kernelReflectionCircuit {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (input : Input) (phaseProvider : VerifiedMath.Quantum.QSP.FinitePhaseProvider AngleType) :
    Circuit (PrimitiveGate (kernelQubits input)) :=
  ((input.source.outerPlan input.fits).compile
    (cp03ProgramWord (phaseProvider input.polynomialRequest)) .pi).closeSymbolsPreserving (fun _ => 0)

theorem kernelReflectionCircuit_denote {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (input : Input) (provider : VerifiedMath.Quantum.QSP.FinitePhaseProvider AngleType) :
    Circuit.denote primitiveGateOperator (kernelReflectionCircuit input provider) =
      Circuit.denote primitiveGateOperator
        ((input.source.outerPlan input.fits).compile
          (cp03ProgramWord (provider input.polynomialRequest)) .pi) :=
  Circuit.denote_closeSymbolsPreserving _ _

/-- CP04 is the same primitive circuit, with a different logical readout. -/
def successfulHistoryCircuit {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (input : Input) (phaseProvider : VerifiedMath.Quantum.QSP.FinitePhaseProvider AngleType) :
    Circuit (PrimitiveGate (kernelQubits input)) :=
  kernelReflectionCircuit input phaseProvider

/-- External phase data carries finite syntax only, not an accuracy claim. -/
def numericalPhaseProvider
    (word : VerifiedMath.Quantum.QSP.Word VerifiedCircuitCore.FinitePhaseAngle) :
    VerifiedMath.Quantum.QSP.FinitePhaseProvider VerifiedCircuitCore.FinitePhaseAngle := fun _ => word

theorem kernelReflectionCircuit_numerical
    (input : Input) (word : VerifiedMath.Quantum.QSP.Word VerifiedCircuitCore.FinitePhaseAngle) :
    kernelReflectionCircuit input (numericalPhaseProvider word) =
      ((input.source.outerPlan input.fits).compile (cp03ProgramWord word) .pi).closeSymbolsPreserving
        (fun _ => 0) := rfl

end QLean.Circuits.FiniteKernelCircuit
