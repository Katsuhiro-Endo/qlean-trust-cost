import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution
import Mathlib
import Mathlib.Tactic

/-!
# Coalescing-walk mathematical specification

This module is deliberately independent of every circuit, register, wire,
encoding, compiler, and correspondence definition.  These are the scientific
objects a human approves.
-/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.CoalescingWalkModel

open Matrix
open scoped BigOperators

noncomputable section

/-- Coordinate-bit width and maximum particle count. -/
structure Parameters where
  q : Nat
  K : Nat
  q_pos : 0 < q
  K_pos : 0 < K

namespace Parameters

/-- Side length of the periodic square lattice. -/
def G (parameters : Parameters) : Nat := 2 ^ parameters.q

theorem G_pos (parameters : Parameters) : 0 < parameters.G := by
  simp [G]

end Parameters

/-- A lattice site.  `finProdFinEquiv` gives its two mathematical coordinates;
this finite linear index is not a circuit encoding or a wire representation. -/
abbrev Site (parameters : Parameters) := Fin (parameters.G * parameters.G)

def siteCoordinates {parameters : Parameters} (site : Site parameters) :
    Fin parameters.G × Fin parameters.G :=
  finProdFinEquiv.symm site

def siteOfCoordinates {parameters : Parameters}
    (coordinates : Fin parameters.G × Fin parameters.G) : Site parameters :=
  finProdFinEquiv coordinates

/-- A nonempty set of at most `K` occupied sites. -/
abbrev Configuration (parameters : Parameters) :=
  { sites : Finset (Site parameters) //
    sites.Nonempty ∧ sites.card ≤ parameters.K }

/-- The two events allowed by the scientific model. -/
inductive Direction
  | right
  | up
  deriving DecidableEq, Fintype

/-- Add one modulo the periodic side length. -/
def increment {parameters : Parameters} (coordinate : Fin parameters.G) :
    Fin parameters.G :=
  ⟨(coordinate.val + 1) % parameters.G,
    Nat.mod_lt _ parameters.G_pos⟩

/-- Move a site one step right or up with periodic boundary conditions. -/
def moveSite {parameters : Parameters}
    (site : Site parameters) (direction : Direction) : Site parameters :=
  let coordinates := siteCoordinates site
  match direction with
  | .right => siteOfCoordinates (coordinates.1, increment coordinates.2)
  | .up => siteOfCoordinates (increment coordinates.1, coordinates.2)

abbrev Event (parameters : Parameters) := Site parameters × Direction

/-- Every occupied site contributes one right and one up event. -/
def events {parameters : Parameters} (input : Configuration parameters) :
    Finset (Event parameters) :=
  input.1.product Finset.univ

/-- Site set after the selected occupied source moves.  Insertion implements
coalescence if the destination is already occupied. -/
def updatedSites {parameters : Parameters}
    (input : Configuration parameters) (event : Event parameters) :
    Finset (Site parameters) :=
  insert (moveSite event.1 event.2) (input.1.erase event.1)

/-- Number of right/up events that take `input` to `output`. -/
def transitionCount {parameters : Parameters}
    (output input : Configuration parameters) : Nat :=
  ((events input).filter fun event => updatedSites input event = output.1).card

/-- Column-vector generator of the coalescing walk. -/
def generator {parameters : Parameters} :
    Matrix (Configuration parameters) (Configuration parameters) ℝ :=
  fun output input =>
    if output = input then -(input.1.card : ℝ)
    else (transitionCount output input : ℝ) / 2

/-- User-controlled scientific input. -/
structure Input (parameters : Parameters) where
  initial : Configuration parameters → ℝ
  duration : ℝ
  tolerance : ℝ

/-- Conditions belonging to the scientific problem, not to a circuit. -/
def Valid {parameters : Parameters} (input : Input parameters) : Prop :=
  input.initial ≠ 0 ∧ 0 ≤ input.duration ∧ 0 < input.tolerance

def siteAt {parameters : Parameters} (configuration : Configuration parameters)
    (slot : Fin configuration.1.card) : Site parameters :=
  ((configuration.1.orderIsoOfFin rfl) slot).1

end
end QLean.MathematicalSpecifications.CoalescingWalkModel

namespace QLean.MathematicalSpecifications.Targets

open Matrix QLean.MathematicalSpecifications.CoalescingWalkModel
open scoped BigOperators

end QLean.MathematicalSpecifications.Targets

namespace QLean.MathematicalSpecifications.CoalescingWalkModel

open Matrix
open scoped BigOperators


end QLean.MathematicalSpecifications.CoalescingWalkModel
