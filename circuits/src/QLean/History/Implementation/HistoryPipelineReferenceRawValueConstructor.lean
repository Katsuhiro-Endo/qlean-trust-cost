import QLean.History.Implementation.HistoryPipelineReferenceEntryDecoder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceRawValueConstructor

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawSemanticCompiler
open HistoryPipelineReferenceEntryDecoder

noncomputable section

/-!
  DevelopmentStage036 is the value-only compiler layer.  It constructs raw records and
  does not claim any of the stronger analytic, wire-admissibility, or P15
  clean-block theorems.  The finite code below is deliberately large enough
  to retain every matrix and initial entry without a caller supplied field.
-/

abbrev ReferenceData036 {Configuration : Type*} [Fintype Configuration] :=
  ReferenceData034 (Configuration := Configuration)

abbrev ReferenceCode036 (Configuration : Type*) :=
  Sum (Configuration × Configuration) Configuration

def referenceCodeValue036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) :
    ReferenceCode036 Configuration → ℚ
  | Sum.inl (output, input) => data.modelQ output input
  | Sum.inr configuration => data.initial configuration

def referenceCodeAt036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration))
    (n : ℕ) : ℚ :=
  if h : n < Fintype.card (ReferenceCode036 Configuration) then
    referenceCodeValue036 data
      ((Fintype.equivFin (ReferenceCode036 Configuration)).symm ⟨n, h⟩)
  else 0

def referenceScientificCodeAt036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration))
    (n : ℕ) : SpectralSamplingProof.Analytic.ScientificAngleExpr :=
  let value := referenceCodeAt036 data n
  .rational value.num value.den value.den_pos

def referenceRawCodeAngleAt036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration))
    (n : ℕ) : AngleExpr :=
  encodedEntryAngle035 (referenceCodeAt036 data n)

def referenceAnalyticCodeAt036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration))
    (n : ℕ) : ℝ :=
  (referenceCodeAt036 data n : ℝ)

def rawTimeSteps036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  data.parameters.physicalClocks

def rawTaylorOrder036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  data.parameters.taylorOrder

def rawDataWidth036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  data.parameters.binaryLabels

def rawGeneratorSignalWidth036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  data.parameters.taylorOrder

def rawGeneratorWorkWidth036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  data.parameters.taylorOrder

def rawHistoryBlocks036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  data.parameters.binaryLabels

def rawOrderWidth036
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData036 (Configuration := Configuration)) : ℕ :=
  SpectralSamplingProof.Analytic.historyOrderWidth (rawTaylorOrder036 data)

/-! Fully applied d=2 positives. -/

/-! Typed negative regressions for the value-only layer. -/

end

end HistoryPipelineReferenceRawValueConstructor
