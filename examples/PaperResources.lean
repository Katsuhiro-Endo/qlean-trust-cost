import QLean.Circuits.CheckpointCircuits
import ResourceCountFormula
import Mathlib.Tactic

open ProbabilityGeneratorQProof
open QLean.Circuits.FiniteScientificCircuitSource
open QLean.Circuits

namespace PaperQ2K2

def parameters : QParameters :=
  { q := 2, K := 2, q_pos := by decide, K_pos := by decide }

def historyParameters : HistoryBlockEncoding.HistorySpec.Parameters :=
  { physicalClocks := 1, taylorOrder := 1, stepSize := 1/6,
    binaryLabels := 2, clockEnd := 3 }

-- Row zero is the upper row: site = x + 4*y. Preserve the evaluated input.
def configuration : QConfiguration parameters :=
  ⟨{(⟨0, by decide⟩ : QSite parameters), (⟨3, by decide⟩ : QSite parameters)}, by decide⟩

def source : FiniteScientificSource :=
  { qParameters := parameters
    historyParameters := historyParameters
    historyWellFormed := by
      norm_num [HistoryBlockEncoding.HistorySpec.WellFormed, historyParameters]
    initial := { entries := [(configuration, 1)] }
    historyBlocks := 2
    historyBlocksPositive := by decide
    binaryLabelsExact := by decide
    clockEndExact := by decide
    stepPositive := by norm_num [historyParameters]
    scaledStepSmall := by norm_num [parameters, historyParameters] }

def input : FiniteKernelCircuit.Input :=
  { source := source
    fits := { clock_fits := by decide, label_fits := by decide }
    epsilon := 1/100
    epsilon_pos := by norm_num
    epsilon_lt_two := by norm_num }

end PaperQ2K2

def main : IO Unit := do
  let input := PaperQ2K2.input
  IO.println "initial_sites=0,3 (upper-left, upper-right)"
  IO.println "q=2 K=2 m=1 h=1/6 T=1/6 d=1 c=3 epsilon=1/100"
  IO.println s!"cp01_qubits={CheckpointCircuits.generatorQubits PaperQ2K2.parameters}"
  IO.println s!"cp01_gates={(CheckpointCircuits.generatorCircuit PaperQ2K2.parameters).gateCount}"
  IO.println s!"cp02_qubits={input.source.historyQubits}"
  IO.println s!"cp02_gates={input.source.historyCircuit.gateCount}"
  IO.println s!"cp03_cp04_qubits={FiniteKernelCircuit.kernelQubits input}"
  IO.println s!"qsp_degree={input.polynomialRequest.degree}"
  IO.println s!"qsp_phase_count={input.polynomialRequest.phaseCount}"
  let s := ResourceCountFormula.fastControlCost
    (input.source.outerPlan input.fits).layout (input.source.outerPlan input.fits).signalCircuit
  IO.println s!"signalCost={s}"
  (← IO.getStdout).flush
  let p := ResourceCountFormula.cachedPhaseCost input
  IO.println s!"phaseCost={p}"
  let l := input.polynomialRequest.degree
  IO.println s!"cp03_cp04_gates={11+4*(l*s+(l+1)*p)+p}"
