import QLean.History.Implementation.HistoryPipelineReferenceRawCompiler

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceRawSemanticCompiler

open Matrix
open HistoryBlockEncoding
open HistoryPipelineReferenceRawCompiler

noncomputable section

/-!
  DevelopmentStage034 keeps the reference carrier proof-free and makes the remaining
  executable boundary explicit.  The current raw P15 packet is a packet of
  angles, widths, wires, and provider parameters; it is not a reference
  `modelQ`/`initial` carrier.  The lemmas below are deliberately generic in
  the proposed raw compiler and in every raw-only scalar observation.  They
  rule out silently erasing a reference datum while a real semantic compiler
  is being connected.
-/

abbrev ReferenceData034 {Configuration : Type*} [Fintype Configuration] :=
  HistoryPipelineReferenceRawCompiler.ReferenceData033 Configuration

/-! This is the exact type a proof-free raw compiler would have to inhabit. -/

/-! Any current P15 semantic scalar that only consumes the raw packet has this
    shape.  It is used only for the indistinguishability argument below. -/

/-! A fully applied nonzero modelQ positive, retained from the d=2
    sensitivity semanticVerification. -/

/-! If a proposed compiler gives the same raw packet to the two explicit d=2
    reference carriers, no raw-only observation can equal both corresponding
    H_hist entries.  This is the exact indistinguishability obstruction for
    an erased/swapped modelQ path; it is not an assertion that an arbitrary
    encoding of modelQ into executable angles has already been constructed. -/

/-! Initial data, nu, and the analytic scale are separate reference inputs.
    These negatives prevent an implementation from silently retaining only
    the modelQ projection. -/

/-! The next theorem is the first missing semantic bridge, stated as a type
    rather than postulated.  It asks for an actual compiler, admissibility
    derivation, and raw-only P15 entry map; DevelopmentStage034 does not manufacture any
    of these from an erased reference packet. -/

end

end HistoryPipelineReferenceRawSemanticCompiler
