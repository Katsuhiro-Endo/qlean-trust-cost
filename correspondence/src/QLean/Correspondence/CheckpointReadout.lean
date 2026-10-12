import QLean.MathematicalSpecifications.PublicCheckpointData
import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution
import VerifiedMath.OperatorRelations
import QLean.Circuits.CheckpointCircuits
import QLean.Circuits.Foundation.Gates
import VerifiedMath.BlockReadout

/-!
# Implementation-independent checkpoint readouts

Every definition in this module computes its result from the operator or
circuit supplied by its caller.  In particular, none of the readouts selects
a benchmark circuit or returns a pre-recorded target behind the scenes.
-/

set_option autoImplicit false

namespace QLean.Correspondence.CheckpointReadout

open Matrix
open VerifiedCircuitCore
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.PublicCheckpoints

noncomputable section

/-- Input and output basis embeddings used to read a square logical block
from a physical operator.  Keeping these as basis embeddings makes the
readout definition compute one supplied operator entry directly, rather than
normalising a large symbolic matrix product. -/
abbrev SquareBinding := VerifiedMath.BlockReadout.SquareBinding

/-- Logical compression of the operator passed by the caller. -/
def squareBlock {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    (binding : SquareBinding logical physical)
    (operator : Matrix physical physical ℂ) : Matrix logical logical ℂ :=
  VerifiedMath.BlockReadout.squareBlock binding operator

/-- Read the probability-generator block of a supplied operator. -/
def generatorBlock {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    (binding : SquareBinding logical physical)
    (operator : Matrix physical physical ℂ) : Matrix logical logical ℂ :=
  squareBlock binding operator

/-- Read the Jennings-history block of a supplied operator. -/
def historyBlock {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    (binding : SquareBinding logical physical)
    (operator : Matrix physical physical ℂ) : Matrix logical logical ℂ :=
  squareBlock binding operator

/-- Read the QSVT logical block of a supplied operator. -/
def qsvtBlock {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    (binding : SquareBinding logical physical)
    (operator : Matrix physical physical ℂ) : Matrix logical logical ℂ :=
  squareBlock binding operator

end

end QLean.Correspondence.CheckpointReadout
