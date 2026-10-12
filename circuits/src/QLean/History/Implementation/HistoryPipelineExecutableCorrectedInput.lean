import QLean.History.Implementation.HistoryPipelineExecutableHistoryRaw
import QLean.History.Integration.HistoryAssemblyP15P44Adapter

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open ProbabilityGeneratorQProof
open HistoryPipelineReferenceAdmissibility041

noncomputable section

def executableRawInput119 (source : AlignedCommonSource119) :
    HistoryAssemblyP15P44Adapter.RawInput145 :=
  { history := executableHistoryRaw119 source
    generator := generatorRaw119 source.toCommonSource119
    sharedQ := source.qParameters.q
    sharedK := source.qParameters.K }

/-- The generator grid width remains independent of the history Taylor
order in the final executable input. -/
@[simp] theorem executableRawInput119_sharedQ
    (source : AlignedCommonSource119) :
    (executableRawInput119 source).sharedQ = source.qParameters.q := by
  rfl

/-- The generator particle cap remains independent of the history block
counts in the final executable input. -/
@[simp] theorem executableRawInput119_sharedK
    (source : AlignedCommonSource119) :
    (executableRawInput119 source).sharedK = source.qParameters.K := by
  rfl

theorem executableHistory_dataWidth119 (source : AlignedCommonSource119) :
    (executableHistoryRaw119 source).dataWidth =
      source.qParameters.generatorDataWidth := by
  change (generatorParameters041 (referenceData119 source)).generatorDataWidth = _
  rw [generatorParameters119_eq]

theorem executableHistory_signalWidth119 (source : AlignedCommonSource119) :
    (executableHistoryRaw119 source).generatorSignalWidth =
      source.qParameters.generatorSignalWidth := by
  change (generatorParameters041 (referenceData119 source)).generatorSignalWidth = _
  rw [generatorParameters119_eq]

theorem executableHistory_workWidth119 (source : AlignedCommonSource119) :
    (executableHistoryRaw119 source).generatorWorkWidth =
      source.qParameters.generatorWorkWidth := by
  change (generatorParameters041 (referenceData119 source)).generatorWorkWidth = _
  rw [generatorParameters119_eq]

theorem executable_sourceTarget_strict119 (source : AlignedCommonSource119) :
    (generatorRaw119 source.toCommonSource119).targetQubits <
      (executableHistoryRaw119 source).qubits := by
  change source.qParameters.ancillaWidth + source.qParameters.systemWidth + 1 <
    qubits041 (referenceData119 source)
  dsimp [qubits041, semanticBase041, workspaceBase041]
  rw [generatorParameters119_eq]
  omega

theorem executable_placementWidths119 (source : AlignedCommonSource119) :
    ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        (generatedBinding119 source.toCommonSource119).parameters
        (executableHistoryRaw119 source).generatorSignalWidth
        (executableHistoryRaw119 source).generatorWorkWidth
        (executableHistoryRaw119 source).dataWidth := by
  refine {
    signal_eq := ?_
    work_eq := ?_
    data_eq := ?_ }
  · exact executableHistory_signalWidth119 source
  · exact executableHistory_workWidth119 source
  · exact executableHistory_dataWidth119 source

theorem executable_raw_coefficient_consistency119
    (source : AlignedCommonSource119)
    (index : Fin (executableHistoryRaw119 source).taylorOrder) :
    (executableHistoryRaw119 source).rawCoefficientAngles index =
      CanonicalHistoryAdapter.compileScientificAngle
        ((executableHistoryRaw119 source).coefficientAngles index) := by
  rfl

theorem executable_raw_idle_consistency119
    (source : AlignedCommonSource119) :
    (executableHistoryRaw119 source).rawIdleCoefficientAngle =
      CanonicalHistoryAdapter.compileScientificAngle
        (executableHistoryRaw119 source).idleCoefficientAngle := by
  rfl

def executableSourceEmbedding119 (source : AlignedCommonSource119) :
    Fin (executableRawInput119 source).generator.targetQubits →
      Fin (executableRawInput119 source).history.qubits :=
  Fin.castLE (Nat.le_of_lt (executable_sourceTarget_strict119 source))

theorem executableSourceEmbedding119_injective (source : AlignedCommonSource119) :
    Function.Injective (executableSourceEmbedding119 source) :=
  Fin.castLE_injective _

def executableCorrectedAdmissible119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryAssemblyP15P44Adapter.CorrectedAdmissible145
      (executableRawInput119 source) := by
  refine ScientificWidthGenericContract.CorrectedAdmissible259.mk
    (analytic := executableHistoryRaw119_admissible source domain)
    (generator := generatorRaw119_admissible source.toCommonSource119)
    (sharedQ_eq := rfl)
    (sharedK_eq_eq := rfl)
    (sourceTarget_le_full := Nat.le_of_lt (executable_sourceTarget_strict119 source))
    (sourceTarget_strict := executable_sourceTarget_strict119 source)
    (placementWidths := ?_)
    (raw_coefficient_consistency := executable_raw_coefficient_consistency119 source)
    (raw_idle_consistency := executable_raw_idle_consistency119 source)
    (sourceEmbedding := executableSourceEmbedding119 source)
    (sourceEmbedding_injective := executableSourceEmbedding119_injective source)
  simpa [executableRawInput119, generatedBinding119] using
    executable_placementWidths119 source

end

end ExecutableHistoryExecutableHistory
