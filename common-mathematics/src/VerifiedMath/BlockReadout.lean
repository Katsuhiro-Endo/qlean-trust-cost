import Mathlib

/-! Generic square and rectangular block readout data. -/

set_option autoImplicit false

namespace VerifiedMath.BlockReadout

noncomputable section

structure SquareBinding (logical physical : Type*)
    [Fintype logical] [Fintype physical] where
  inputEmbedding : logical ↪ physical
  outputEmbedding : logical ↪ physical

def squareBlock {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    (binding : SquareBinding logical physical)
    (operator : Matrix physical physical ℂ) : Matrix logical logical ℂ :=
  fun output input =>
    operator (binding.outputEmbedding output) (binding.inputEmbedding input)

end

end VerifiedMath.BlockReadout
