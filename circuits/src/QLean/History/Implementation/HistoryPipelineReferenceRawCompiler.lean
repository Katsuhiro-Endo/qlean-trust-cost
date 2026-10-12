import QLean.History.Implementation.HistoryPipelineCanonicalReferenceInput
import QLean.History.Integration.HistoryAssemblyP15P44Adapter

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceRawCompiler

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore

noncomputable section

/-!
  This module records the constructive boundary exposed by the current
  executable input types.  `ReferenceData032` is the common mathematical
  source; it is not paired with an independently supplied raw input.
  The numerical domain below is deliberately theorem-side data only.  The
  raw compiler is not declared by choosing a raw packet or by storing a
  desired entry equality.
-/

abbrev ReferenceData033 (Configuration : Type*) [Fintype Configuration] :=
  HistoryPipelineCanonicalReferenceInput.ReferenceData032 Configuration

def referenceAlpha033
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData033 Configuration) : ℝ :=
  HistoryPipelineCanonicalReferenceInput.referenceAlpha032 data

/-! The first unresolved constructor is made explicit as a type, without
    manufacturing a value of that type. -/

/-! A fully applied d=2 semantic semanticVerification.  It is a regression/negative for an
    erased raw compiler: the old matrix semantics retain modelQ. -/

/-! Constructor inventory used by the blocked synthesis boundary. -/

end

end HistoryPipelineReferenceRawCompiler
