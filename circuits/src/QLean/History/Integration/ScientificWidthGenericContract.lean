import QLean.History.HistoryP15GeneratedProviderInternalBinding226
import QLean.History.Integration.HistoryIndexCast.HistoryP15P16FinCastSemanticBridgeEstablishedBridge
import QLean.History.HistoryInternalP17P44Certificate
import QLean.Spectral.Circuits.HistoryP15FullClean
import QLean.Spectral.Circuits.HistoryP15H2CleanBridge
import QLean.History.HistoryAnalyticParameters194

/-! Parameter-general scientific-width contract, separated from fixed examples. -/

set_option autoImplicit false

namespace ScientificWidthGenericContract

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ProbabilityGeneratorQProof
open ExecutableHistoryData
open HistoryRawSchema
open HistoryAnalyticParameterExistence194

noncomputable section

abbrev RawInput259 := ExecutableHistoryData.RawP15ExecutableData225

structure CorrectedAdmissible259 (input : RawInput259) where
  analytic : HistoryRawSchema.HistoryP15P16Admissible203 input.history
  generator : GeneratorRawSchema.HistoryP17P44Admissible206 input.generator
  sharedQ_eq : input.sharedQ = input.generator.q
  sharedK_eq_eq : input.sharedK = input.generator.K
  sourceTarget_le_full : input.generator.targetQubits ≤ input.history.qubits
  sourceTarget_strict : input.generator.targetQubits < input.history.qubits
  placementWidths :
    ((GeneratorRawSchema.generatedP17P44Binding206 input.generator generator).parameters).ProbabilityGeneratorCanonicalPlacementWidths
      input.history.generatorSignalWidth input.history.generatorWorkWidth
      input.history.dataWidth
  raw_coefficient_consistency :
    ∀ index, input.history.rawCoefficientAngles index =
      CanonicalHistoryAdapter.compileScientificAngle
        (input.history.coefficientAngles index)
  raw_idle_consistency :
    input.history.rawIdleCoefficientAngle =
      CanonicalHistoryAdapter.compileScientificAngle input.history.idleCoefficientAngle
  sourceEmbedding : Fin input.generator.targetQubits → Fin input.history.qubits
  sourceEmbedding_injective : Function.Injective sourceEmbedding

def correctedLayout259
    (input : RawInput259)
    (admissible : CorrectedAdmissible259 input) :=
  HistoryRawSchema.layout203 input.history admissible.analytic

noncomputable def correctedGeneratorParameters259
    (input : RawInput259)
    (admissible : CorrectedAdmissible259 input) :
    QParameters :=
  (GeneratorRawSchema.generatedP17P44Binding206 input.generator
    admissible.generator).parameters

theorem correctedCleanEvidence259
    (input : RawInput259)
    (admissible : CorrectedAdmissible259 input) :
    HistoryP15PostQ10Evidence (correctedLayout259 input admissible) := by
  let l2 := HistoryIndexCast.history_taylor_l2_evidence207 input.history
    admissible.analytic
  exact {
    clock := {
      clockTimeLessThan := {
        widthPositive := l2.clockTimeLessThan.widthPositive
        lhsRhsDifferent := l2.clockTimeLessThan.lhsRhsDifferent
        lhsBorrowDifferent := l2.clockTimeLessThan.lhsBorrowDifferent
        rhsBorrowDifferent := l2.clockTimeLessThan.rhsBorrowDifferent
        targetLhsDifferent := l2.clockTimeLessThan.targetLhsDifferent
        targetRhsDifferent := l2.clockTimeLessThan.targetRhsDifferent
        targetBorrowDifferent := l2.clockTimeLessThan.targetBorrowDifferent }
      clockIdleEndLessThan := {
        widthPositive := l2.clockIdleEndLessThan.widthPositive
        lhsRhsDifferent := l2.clockIdleEndLessThan.lhsRhsDifferent
        lhsBorrowDifferent := l2.clockIdleEndLessThan.lhsBorrowDifferent
        rhsBorrowDifferent := l2.clockIdleEndLessThan.rhsBorrowDifferent
        targetLhsDifferent := l2.clockIdleEndLessThan.targetLhsDifferent
        targetRhsDifferent := l2.clockIdleEndLessThan.targetRhsDifferent
        targetBorrowDifferent := l2.clockIdleEndLessThan.targetBorrowDifferent } }
    branch_ne_ltIdleEnd := l2.branch_ne_ltIdleEnd
    branch_ne_coefficientSignal := l2.branch_ne_coefficientSignal
    ltIdleEnd_ne_coefficientSignal := l2.ltIdleEnd_ne_coefficientSignal }

end

end ScientificWidthGenericContract
