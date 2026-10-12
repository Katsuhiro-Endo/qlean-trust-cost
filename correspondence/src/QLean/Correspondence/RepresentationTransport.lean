import QLean.MathematicalSpecifications.CoalescingWalkModel
import Mathlib.Tactic
import QLean.Generator.Analysis.QGenerator

/-!
# Explicit transport between the approved model and circuit representations

This module owns no mathematical model and no circuit construction.  It gives
the explicit equivalences used to transport the independently approved finite
types into the legacy circuit-domain representation.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace QLean.Correspondence.RepresentationTransport

open Matrix
open scoped BigOperators Norms.Operator

noncomputable section

/-- Changing the cardinality proof and casting the finite index does not
change the selected element. -/
theorem orderIsoOfFin_cast_value
    {alpha : Type*} [LinearOrder alpha] (sites : Finset alpha)
    {count : Nat} (cardinality : sites.card = count) (slot : Fin count) :
    ((sites.orderIsoOfFin rfl) (Fin.cast cardinality.symm slot)).1 =
      ((sites.orderIsoOfFin cardinality) slot).1 := by
  subst count
  rfl

end

end QLean.Correspondence.RepresentationTransport
