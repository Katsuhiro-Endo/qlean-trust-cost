import QLean.History.Implementation.HistoryPipelineCompatiblePhysicalM10

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineCanonicalReferenceInput

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore

noncomputable section

/-!  This is the common reference-data layer.  It carries only the old
    mathematical input and its proof-free rational data.  The theorem-side
    well-formedness proof is deliberately separate.  In particular, no
    independently supplied RawInput145 or CertifiedM13Input is stored here. -/

structure ReferenceData032 (Configuration : Type*) [Fintype Configuration] where
  parameters : HistoryBlockEncoding.HistorySpec.Parameters
  modelQ : Matrix Configuration Configuration ℚ
  /-- The reference right-hand-side data, in the rational convention of the
      old history construction.  It is kept separate from any proof object. -/
  initial : Configuration → ℚ
  omegaH : ℝ
  nu : ℝ

def referenceAlpha032
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData032 Configuration) : ℝ :=
  HistoryBlockEncoding.HistoryLCU.alphaH data.parameters.taylorOrder data.omegaH

end

end HistoryPipelineCanonicalReferenceInput
