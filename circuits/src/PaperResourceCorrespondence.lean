import QLean.Circuits.CheckpointCircuits
import QLean.History.Implementation.HistoryPipelineFiniteScientificP05Bridge
import ResourceCountFormula

open VerifiedCircuitCore
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open ExecutableHistoryFiniteScientificH3 ExecutableHistoryFiniteCorrectedP05
open ExecutableHistoryFiniteScientificP05Bridge

namespace PaperResourceCorrespondence

theorem gateCount_cast {n m : Nat} (h : n = m) (c : Circuit (PrimitiveGate n)) :
    (h ▸ c).gateCount = c.gateCount := by
  cases h
  rfl

theorem historyCount_public (input : QLean.Circuits.CheckpointCircuits.ExecutableInput) :
    (finiteScientificCorrectedP05Circuit119 input.source).gateCount =
      (QLean.Circuits.CheckpointCircuits.historyCircuit input).gateCount := by
  have first := congrArg Circuit.gateCount
    (finiteScientificCorrectedP05_eq_certified input.source input.domain)
  rw [gateCount_cast, certifiedPlan_compile_eq] at first
  have second := congrArg List.length
    (finiteCorrectedP05CertifiedProjection119_flatten_eq input.source input.domain)
  change (finiteCorrectedP05CertifiedProjection119 input.source input.domain).gateCount =
    (correctedP05Component119 input.source input.domain).circuit.gateCount at second
  have combined := first.trans second
  simpa only [QLean.Circuits.CheckpointCircuits.historyCircuit,
    QLean.Circuits.CheckpointCircuits.buildHistoryCircuit,
    QLean.Circuits.CheckpointCircuits.cp02HistoryCircuit,
    Circuit.specializeSymbols, Circuit.gateCount_mapGates] using combined

theorem historyWidth_public (input : QLean.Circuits.CheckpointCircuits.ExecutableInput) :
    finiteScientificHistoryQubits119 input.source =
      QLean.Circuits.CheckpointCircuits.historyQubits input :=
  finiteScientificHistoryQubits119_eq input.source

theorem kernelCount_public (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    ResourceCountFormula.totalCount input =
      (QLean.Circuits.CheckpointCircuits.kernelReflectionCircuit input
        VerifiedMath.Quantum.QSP.defaultPhaseProvider).gateCount :=
  ResourceCountFormula.totalCount_correct input

theorem successfulHistoryCount_public (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    ResourceCountFormula.totalCount input =
      (QLean.Circuits.CheckpointCircuits.successfulHistoryCircuit input
        VerifiedMath.Quantum.QSP.defaultPhaseProvider).gateCount :=
  ResourceCountFormula.totalCount_cp04_correct input

end PaperResourceCorrespondence
