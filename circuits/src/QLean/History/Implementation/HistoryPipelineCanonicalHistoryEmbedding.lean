import QLean.History.Implementation.HistoryPipelineP18Final
import QLean.History.Implementation.HistoryPipelineFiniteHistoryBasis
import QLean.Generator.Analysis.QConfigurationEnumeration

/-!
Explicit configuration numbering for the history embedding.  The old
abstract history system uses `Fintype.equivFin`; the finite compiler uses the
bitmask numbering.  These can differ, so this module records their exact
permutation.  The permutation is proof-only, not evaluated by the compiler.
-/

set_option autoImplicit false
set_option warningAsError true

namespace ExecutableHistoryExecutableP18

open ExecutableHistoryExecutableHistory
open ExecutableHistoryHistoryEmbedding
open ProbabilityGeneratorQProof
open VerifiedCircuitCore

def canonicalOldHistoryIndex119
    (source : AlignedCommonSource119)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) : OldHistoryIndex119 source :=
  { clock := index.clock
    state :=
      { label := index.order
        configuration :=
          (configurationEquivCard source.qParameters).symm index.state } }

noncomputable def legacyHistoryIndexOfCanonical119
    (source : AlignedCommonSource119)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) :=
  { index with state := canonicalToLegacyIndex source.qParameters index.state }

theorem legacyHistoryIndex_decode119
    (source : AlignedCommonSource119)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    (ExecutableHistoryReferenceM10Bridge.indexEquiv
      source.historyParameters).symm
        (legacyHistoryIndexOfCanonical119 source index) =
      canonicalOldHistoryIndex119 source index := by
  cases index with
  | mk clock order state =>
      simp [legacyHistoryIndexOfCanonical119, canonicalOldHistoryIndex119,
        ExecutableHistoryReferenceM10Bridge.indexEquiv,
        ExecutableHistoryReferenceM10Bridge.configurationEquiv,
        legacyDecode_reindexed]

/-- This source-level bridge is intentionally noncomputable because the
scientific layout itself is a proof-bearing object.  Its finite write body
has the same result as the old embedding after the explicit reindexing. -/
noncomputable def canonicalHistoryPhysicalBasis119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    QubitBasis (ExecutableRaw119 source).history.qubits :=
  let oldIndex := canonicalOldHistoryIndex119 source index
  finiteHistoryBasisAtRegisters
    (ExecutableLayout119 source domain).data
    (ExecutableLayout119 source domain).clock
    (ExecutableLayout119 source domain).order
    (dataBits119 source oldIndex.state.configuration)
    (clockBits119 source fits oldIndex)
    (orderBits119 source fits oldIndex)

theorem canonicalHistoryPhysicalBasis119_reindexed
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    canonicalHistoryPhysicalBasis119 source domain fits index =
      executableP18HistoryEmbedding119 source domain fits
        (legacyHistoryIndexOfCanonical119 source index) := by
  change canonicalHistoryPhysicalBasis119 source domain fits index =
    executableHistoryBasis119 source domain fits
      ((ExecutableHistoryReferenceM10Bridge.indexEquiv
        source.historyParameters).symm
        (legacyHistoryIndexOfCanonical119 source index))
  rw [legacyHistoryIndex_decode119]
  exact finiteHistoryBasisAtRegisters_scientific_eq source domain fits _

end ExecutableHistoryExecutableP18
