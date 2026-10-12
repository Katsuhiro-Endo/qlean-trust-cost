import QLean.Correspondence.HistoryLinearSystemTransport
import QLean.Correspondence.RepresentationTransport
import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution
import QLean.MathematicalSpecifications.PublicCheckpointData
import VerifiedMath.OperatorRelations
import QLean.MathematicalSpecifications.CoalescingWalkModel
import Mathlib.Tactic
import QLean.Generator.Analysis.QGenerator
import QLean.SignalProcessing.M13bPrimitiveCandidate
import QLean.SignalProcessing.JenningsM13AnalyticBounds
import QLean.History.JenningsExecutableHistoryDomain
import QLean.MathematicalSpecifications.HistoryLinearSystem

/-!
# Approved benchmark history correspondence

The theorem in this file identifies the executable Jennings data with the
independent benchmark history system after the one explicit configuration
reindexing.  Consequently every matrix and right-hand-side entry is fixed by
the human mathematical specification rather than by a circuit-side target.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Correspondence.BenchmarkHistoryCorrespondence

open ExecutableHistoryExecutableP18

noncomputable section

theorem historySpec_ext
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    {left right : JenningsHistory.HistorySpec d clockCount taylorOrder
      physicalSteps orderCount}
    (step_eq : left.step = right.step)
    (generator_eq : left.generator = right.generator)
    (initial_eq : left.initial = right.initial) : left = right := by
  cases left with
  | mk leftStep leftGenerator leftInitial leftOrder leftPhysicalPos
      leftPhysicalLt =>
    cases right with
    | mk rightStep rightGenerator rightInitial rightOrder rightPhysicalPos
      rightPhysicalLt =>
    simp only at step_eq generator_eq initial_eq
    subst rightStep
    subst rightGenerator
    subst rightInitial
    rfl

end

end QLean.Correspondence.BenchmarkHistoryCorrespondence
