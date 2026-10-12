import QLean.Generator.Analysis.QEncoding
import QLean.Circuits.Foundation.QubitBasisEncoding

/-!
Computable candidate enumeration for finite lattice configurations.
The ordering is the explicit little-endian bitmask order, not
`Fintype.equivFin`'s noncomputable choice.  A later adapter must use this same
ordering on both the history-system and extraction sides.
-/

set_option autoImplicit false
set_option warningAsError true

namespace ProbabilityGeneratorQProof

open VerifiedCircuitCore

/-- The occupancy bitmask of one configuration. -/
def configurationBits (p : QParameters) (configuration : QConfiguration p) :
    QubitBasis (p.G * p.G) :=
  fun site => decide (site ∈ configuration.val)

/-- Computable little-endian code for a configuration. -/
def configurationCode (p : QParameters) (configuration : QConfiguration p) :
    Fin (2 ^ (p.G * p.G)) :=
  qubitBasisLittleEndianEquiv _ (configurationBits p configuration)

/-- Decode a bitmask without imposing the particle-number bound. -/
def decodedConfigurationSet (p : QParameters)
    (code : Fin (2 ^ (p.G * p.G))) : Finset (QSite p) :=
  Finset.univ.filter fun site =>
    qubitBasisOfLittleEndianIndex code site = true

theorem decodedConfigurationSet_code (p : QParameters)
    (configuration : QConfiguration p) :
    decodedConfigurationSet p (configurationCode p configuration) =
      configuration.val := by
  ext site
  simp only [decodedConfigurationSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change ((qubitBasisLittleEndianEquiv _).symm
      ((qubitBasisLittleEndianEquiv _) (configurationBits p configuration))) site =
        true ↔ site ∈ configuration.val
  rw [Equiv.symm_apply_apply]
  simp [configurationBits]

theorem decodedConfigurationSet_injective (p : QParameters) :
    Function.Injective (decodedConfigurationSet p) := by
  intro left right equal
  have bitsEqual : qubitBasisOfLittleEndianIndex left =
      qubitBasisOfLittleEndianIndex right := by
    funext site
    have atSite := congrArg (fun set : Finset (QSite p) => site ∈ set) equal
    have truth :
        (qubitBasisOfLittleEndianIndex left site = true) ↔
          (qubitBasisOfLittleEndianIndex right site = true) := by
      simpa [decodedConfigurationSet] using atSite
    cases hl : qubitBasisOfLittleEndianIndex left site <;>
      cases hr : qubitBasisOfLittleEndianIndex right site <;>
      simp_all
  exact (qubitBasisLittleEndianEquiv _).symm.injective bitsEqual

/-- Invalid masks are dropped; valid masks become typed configurations. -/
def configurationOfValidCode (p : QParameters)
    (code : Fin (2 ^ (p.G * p.G))) : Option (QConfiguration p) :=
  let selected := decodedConfigurationSet p code
  if h : 1 ≤ selected.card ∧ selected.card ≤ p.K then
    some ⟨selected, h⟩
  else none

theorem configurationOfValidCode_code (p : QParameters)
    (configuration : QConfiguration p) :
    configurationOfValidCode p (configurationCode p configuration) =
      some configuration := by
  simp [configurationOfValidCode, decodedConfigurationSet_code,
    configuration.property]

theorem configurationOfValidCode_some_injective (p : QParameters)
    {left right : Fin (2 ^ (p.G * p.G))}
    {configuration : QConfiguration p}
    (leftValue : configurationOfValidCode p left = some configuration)
    (rightValue : configurationOfValidCode p right = some configuration) :
    left = right := by
  have decodeOfSome (code : Fin (2 ^ (p.G * p.G)))
      (value : configurationOfValidCode p code = some configuration) :
      decodedConfigurationSet p code = configuration.val := by
    unfold configurationOfValidCode at value
    dsimp at value
    split_ifs at value with valid
    · exact congrArg Subtype.val (Option.some.inj value)
  apply decodedConfigurationSet_injective p
  exact (decodeOfSome left leftValue).trans (decodeOfSome right rightValue).symm

/-- Finite, executable list of admissible configurations. -/
def enumeratedConfigurations (p : QParameters) : List (QConfiguration p) :=
  (List.finRange (2 ^ (p.G * p.G))).filterMap
    (configurationOfValidCode p)

theorem configuration_mem_enumeration (p : QParameters)
    (configuration : QConfiguration p) :
    configuration ∈ enumeratedConfigurations p := by
  apply List.mem_filterMap.mpr
  refine ⟨configurationCode p configuration, by simp, ?_⟩
  simp [configurationOfValidCode, decodedConfigurationSet_code,
    configuration.property]

private theorem nodup_filterMap_of_injective_some {α β : Type*}
    (function : α → Option β) (values : List α)
    (unique : ∀ left right output,
      function left = some output → function right = some output →
        left = right)
    (noDuplicates : values.Nodup) :
    (values.filterMap function).Nodup := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
      have headNotTail := (List.nodup_cons.mp noDuplicates).1
      have tailNodup := (List.nodup_cons.mp noDuplicates).2
      cases headValue : function head with
      | none =>
          simpa [List.filterMap_cons, headValue] using
            inductionHypothesis tailNodup
      | some output =>
          simp only [List.filterMap_cons, headValue]
          apply List.nodup_cons.mpr
          constructor
          · intro outputInTail
            obtain ⟨other, otherInTail, otherValue⟩ :=
              List.mem_filterMap.mp outputInTail
            have same := unique head other output headValue otherValue
            apply headNotTail
            simpa [same] using otherInTail
          · exact inductionHypothesis tailNodup

theorem enumeratedConfigurations_nodup (p : QParameters) :
    (enumeratedConfigurations p).Nodup := by
  exact nodup_filterMap_of_injective_some
    (configurationOfValidCode p) (List.finRange _)
    (by
      intro left right output leftValue rightValue
      exact configurationOfValidCode_some_injective p leftValue rightValue)
    (List.nodup_finRange _)

/-- Computable and canonical (bitmask-order) index of every legal
configuration.  This is deliberately not `Fintype.equivFin`, whose order is
chosen noncomputably. -/
def configurationEquivFin (p : QParameters) :
    QConfiguration p ≃ Fin (enumeratedConfigurations p).length :=
  ((enumeratedConfigurations_nodup p).getEquivOfForallMemList
    (enumeratedConfigurations p) (configuration_mem_enumeration p)).symm

theorem configurationCount_eq (p : QParameters) :
    Fintype.card (QConfiguration p) =
      (enumeratedConfigurations p).length := by
  simpa using Fintype.card_congr (configurationEquivFin p)

/-- The same computational numbering, expressed at the existing cardinality
type used by the history implementation. -/
def configurationEquivCard (p : QParameters) :
    QConfiguration p ≃ Fin (Fintype.card (QConfiguration p)) :=
  (configurationEquivFin p).trans
    (Equiv.cast (congrArg Fin (configurationCount_eq p).symm))

/-- Proof-only permutation from the explicit numerical numbering to the
legacy noncomputable `Fintype.equivFin` numbering.  Numerical gate generation
must never evaluate this permutation; its role is to transport established
logical statements while the physical construction is reindexed. -/
noncomputable def canonicalToLegacyIndex (p : QParameters) :
    Fin (Fintype.card (QConfiguration p)) ≃
      Fin (Fintype.card (QConfiguration p)) :=
  (configurationEquivCard p).symm.trans
    (Fintype.equivFin (QConfiguration p))

theorem legacyDecode_reindexed (p : QParameters)
    (index : Fin (Fintype.card (QConfiguration p))) :
    (Fintype.equivFin (QConfiguration p)).symm
      (canonicalToLegacyIndex p index) =
        (configurationEquivCard p).symm index := by
  simp [canonicalToLegacyIndex]

end ProbabilityGeneratorQProof
