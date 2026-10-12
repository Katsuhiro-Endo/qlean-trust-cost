import QLean.History.Integration.ConcreteHistoryInput.Concrete

/-! Positive M13 scientific admissibility and consequences. -/

open scoped BigOperators
noncomputable section

namespace TypedNegativeCases

open JenningsHistory
open GramOperator
open ConcreteHistoryInput

/- The admissibility record is the typed bridge to the actual M13c data.
   Every rejection below carries the fully applied concrete formula/error/
   success theorem in its result, so no certificate is a name-only scan. -/
structure M13Admissible (d c r m R : Nat) where
  system : HistorySpec d c r m R
  alpha : ℝ
  nu : ℝ
  x : HistoryVector d c R
  hwell : wellPosed (enlargedMatrix system alpha nu)
  hdet : IsUnit (enlargedMatrix system alpha nu).det
  hraw : linearApply (historyMatrix system) x = historyRhs system
  hrhs : rhsNorm system ≠ 0
  hα : alpha ≠ 0
  hν : nu ≠ 0
  hνpos : 0 < nu
  hαpos : 0 < alpha
  hb : unitNorm (bPlus system)
  hXpos : 0 < unitNormSquared (m13XAlpha system alpha x)

def actualTarget {d c r m R : Nat} (A : M13Admissible d c r m R) :
    ExtE d c R :=
  m13ConcreteIdealHistoryTarget A.system A.alpha A.nu A.x

def actualBasis {d c R : Nat} : ExtE d c R :=
  m13ExtensionBasisE (d := d) (c := c) (R := R)

end TypedNegativeCases
