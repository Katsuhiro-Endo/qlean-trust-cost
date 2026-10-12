import Mathlib

/-!
# Circuit-independent linear algebra for the generator model

The scientific generator uses only finite complex vectors and matrices.
Defining those aliases directly keeps the model/specification dependency
closure independent of circuit syntax while remaining definitionally equal to
the corresponding aliases used by the circuit semantics.
-/

namespace ProbabilityGeneratorQProof

/-- A finite state vector used by the generator analysis. -/
abbrev State (basis : Type*) := basis → ℂ

/-- A finite linear operator used by the generator analysis. -/
abbrev Operator (basis : Type*) := Matrix basis basis ℂ

end ProbabilityGeneratorQProof
