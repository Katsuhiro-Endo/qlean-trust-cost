import QLean.Correspondence.RepresentationTransport
import QLean.MathematicalSpecifications.DelimiterEncoding
import Mathlib.Tactic

/-!
# Parameter-general representation transport

This module constructs, from every independently approved pair `q,K`, the
corresponding circuit-side finite types.  It contains no benchmark constants.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace QLean.Correspondence.GeneralRepresentationTransport

open Matrix

noncomputable section

open QLean.MathematicalSpecifications.CoalescingWalkModel
open QLean.MathematicalSpecifications.Targets
open ProbabilityGeneratorQProof

/-- The circuit parameter record built from the same independent `q,K`. -/
def parametersToCircuit (parameters : Parameters) : QParameters where
  q := parameters.q
  K := parameters.K
  q_pos := parameters.q_pos
  K_pos := parameters.K_pos

@[simp] theorem parametersToCircuit_q (parameters : Parameters) :
    (parametersToCircuit parameters).q = parameters.q := rfl

@[simp] theorem parametersToCircuit_K (parameters : Parameters) :
    (parametersToCircuit parameters).K = parameters.K := rfl

/-- The independent delimiter register and the circuit system register have
the same width for every admissible `q,K`. -/
theorem delimiterWidth_eq_systemWidth (parameters : Parameters) :
    delimiterWidth parameters = (parametersToCircuit parameters).systemWidth := by
  rfl

/-- Representation equivalence for the complete delimiter-word space,
including invalid delimiter codes. -/
def delimiterWordEquiv (parameters : Parameters) :
    DelimiterWord parameters ≃
      RegisterBasis (parametersToCircuit parameters).systemWidth where
  toFun bits wire := bits
    (Fin.cast (delimiterWidth_eq_systemWidth parameters).symm wire)
  invFun bits wire := bits
    (Fin.cast (delimiterWidth_eq_systemWidth parameters) wire)
  left_inv bits := by funext wire; simp
  right_inv bits := by funext wire; simp

theorem siteCardinality_eq (parameters : Parameters) :
    parameters.G * parameters.G =
      (parametersToCircuit parameters).G *
        (parametersToCircuit parameters).G := rfl

/-- Lattice sites are transported without changing their finite value. -/
def siteEquiv (parameters : Parameters) :
    Site parameters ≃ QSite (parametersToCircuit parameters) :=
  Equiv.cast (congrArg Fin (siteCardinality_eq parameters))

/-- The site transport preserves the canonical order used to enumerate an
occupied configuration. -/
def siteOrderIso (parameters : Parameters) :
    Site parameters ≃o QSite (parametersToCircuit parameters) where
  toEquiv := siteEquiv parameters
  map_rel_iff' := by
    intro left right
    rfl

/-- Restrict the ordered site transport to one occupied finite set. -/
def mappedSiteSubtypeOrderIso (parameters : Parameters)
    (sites : Finset (Site parameters)) :
    {site // site ∈ sites} ≃o
      {site // site ∈ sites.map (siteEquiv parameters).toEmbedding} where
  toFun site :=
    ⟨siteEquiv parameters site.1,
      Finset.mem_map.mpr ⟨site.1, site.2, rfl⟩⟩
  invFun site := by
    refine ⟨(siteEquiv parameters).symm site.1, ?_⟩
    obtain ⟨source, sourceMember, mapped⟩ := Finset.mem_map.mp site.2
    have sourceEq : (siteEquiv parameters).symm site.1 = source := by
      rw [← mapped]
      simp
    simpa [sourceEq] using sourceMember
  left_inv site := by
    apply Subtype.ext
    simp
  right_inv site := by
    apply Subtype.ext
    simp
  map_rel_iff' := by
    intro left right
    exact (siteOrderIso parameters).le_iff_le

/-- Mathematical configurations and executable configurations differ only in
the presentation of non-emptiness. -/
def configurationEquiv (parameters : Parameters) :
    Configuration parameters ≃ QConfiguration (parametersToCircuit parameters) where
  toFun configuration :=
    ⟨configuration.1.map (siteEquiv parameters).toEmbedding,
      by simpa using Finset.one_le_card.mpr configuration.2.1,
      by simpa using configuration.2.2⟩
  invFun configuration :=
    ⟨configuration.1.map (siteEquiv parameters).symm.toEmbedding,
      ⟨by
        apply Finset.one_le_card.mp
        simpa using configuration.2.1,
       by simpa using configuration.2.2⟩⟩
  left_inv configuration := by
    apply Subtype.ext
    ext site
    simp
  right_inv configuration := by
    apply Subtype.ext
    ext site
    simp

@[simp] theorem configurationEquiv_sites (parameters : Parameters)
    (configuration : Configuration parameters) :
    (configurationEquiv parameters configuration).1 =
      configuration.1.map (siteEquiv parameters).toEmbedding := rfl

/-- Ascending occupied-site slots agree after the parameter-general
representation transport. -/
theorem siteAt_transport (parameters : Parameters)
    (configuration : Configuration parameters)
    (slot : Fin configuration.1.card) :
    ProbabilityGeneratorQProof.QConfiguration.siteAt
        (configurationEquiv parameters configuration)
        (Fin.cast (by simp [configurationEquiv]) slot) =
      siteEquiv parameters
        (QLean.MathematicalSpecifications.CoalescingWalkModel.siteAt
          configuration slot) := by
  let sites := configuration.1
  have enumerationEquality :
      (sites.map (siteEquiv parameters).toEmbedding).orderIsoOfFin
          (Finset.card_map (siteEquiv parameters).toEmbedding) =
        (sites.orderIsoOfFin rfl).trans
          (mappedSiteSubtypeOrderIso parameters sites) :=
    Subsingleton.elim _ _
  have atSlot := DFunLike.congr_fun enumerationEquality slot
  calc
    ProbabilityGeneratorQProof.QConfiguration.siteAt
        (configurationEquiv parameters configuration)
        (Fin.cast (by simp [configurationEquiv]) slot) =
      ((sites.map (siteEquiv parameters).toEmbedding).orderIsoOfFin
          (Finset.card_map (siteEquiv parameters).toEmbedding) slot).1 := by
        exact QLean.Correspondence.RepresentationTransport.orderIsoOfFin_cast_value
          (sites.map (siteEquiv parameters).toEmbedding)
          (Finset.card_map (siteEquiv parameters).toEmbedding) slot
    _ = siteEquiv parameters
        (QLean.MathematicalSpecifications.CoalescingWalkModel.siteAt
          configuration slot) := by
      simpa [ProbabilityGeneratorQProof.QConfiguration.siteAt,
        QLean.MathematicalSpecifications.CoalescingWalkModel.siteAt, sites,
        mappedSiteSubtypeOrderIso] using congrArg Subtype.val atSlot

def directionEquiv : Direction ≃ QDirection where
  toFun
    | .right => .right
    | .up => .up
  invFun
    | .right => .right
    | .up => .up
  left_inv direction := by cases direction <;> rfl
  right_inv direction := by cases direction <;> rfl

def eventEquiv (parameters : Parameters) :
    Event parameters ≃ QEvent (parametersToCircuit parameters) :=
  (siteEquiv parameters).prodCongr directionEquiv

@[simp] theorem eventEquiv_apply (parameters : Parameters)
    (event : Event parameters) :
    eventEquiv parameters event =
      (siteEquiv parameters event.1, directionEquiv event.2) := rfl

theorem moveSite_transport (parameters : Parameters)
    (site : Site parameters) (direction : Direction) :
    ProbabilityGeneratorQProof.moveSite
        (siteEquiv parameters site) (directionEquiv direction) =
      siteEquiv parameters (moveSite site direction) := by
  apply Fin.ext
  cases direction <;> rfl

/-- The mathematical successor configuration for an active event. -/
def updatedConfiguration (parameters : Parameters)
    (input : Configuration parameters) (event : Event parameters)
    (active : event.1 ∈ input.1) : Configuration parameters :=
  ⟨updatedSites input event,
    by
      constructor
      · exact ⟨moveSite event.1 event.2, Finset.mem_insert_self _ _⟩
      · calc
          (updatedSites input event).card ≤ (input.1.erase event.1).card + 1 :=
            Finset.card_insert_le _ _
          _ = input.1.card := by
            rw [Finset.card_erase_of_mem active]
            exact Nat.sub_add_cancel (Finset.one_le_card.mpr input.2.1)
          _ ≤ parameters.K := input.2.2⟩

theorem active_event_transport (parameters : Parameters)
    (input : Configuration parameters) (event : Event parameters)
    (active : event.1 ∈ input.1) :
    ProbabilityGeneratorQProof.updateConfiguration
        (configurationEquiv parameters input)
        (eventEquiv parameters event) =
      configurationEquiv parameters
        (updatedConfiguration parameters input event active) := by
  rcases event with ⟨site, direction⟩
  have transportedActive :
      siteEquiv parameters site ∈
        (configurationEquiv parameters input).1 := by
    exact Finset.mem_map.mpr ⟨site, active, rfl⟩
  apply Subtype.ext
  cases direction with
  | right =>
      simp only [ProbabilityGeneratorQProof.updateConfiguration,
        eventEquiv_apply]
      rw [dif_pos transportedActive]
      simp only [ProbabilityGeneratorQProof.updateSiteSet]
      rw [if_pos transportedActive]
      have directionRight :
          directionEquiv Direction.right =
            ProbabilityGeneratorQProof.QDirection.right := rfl
      rw [directionRight]
      rw [show
        ProbabilityGeneratorQProof.moveSite (siteEquiv parameters site)
            ProbabilityGeneratorQProof.QDirection.right =
          siteEquiv parameters
            (moveSite site Direction.right)
        from moveSite_transport parameters site Direction.right]
      simp [configurationEquiv, updatedConfiguration, updatedSites]
  | up =>
      simp only [ProbabilityGeneratorQProof.updateConfiguration,
        eventEquiv_apply]
      rw [dif_pos transportedActive]
      simp only [ProbabilityGeneratorQProof.updateSiteSet]
      rw [if_pos transportedActive]
      have directionUp :
          directionEquiv Direction.up =
            ProbabilityGeneratorQProof.QDirection.up := rfl
      rw [directionUp]
      rw [show
        ProbabilityGeneratorQProof.moveSite (siteEquiv parameters site)
            ProbabilityGeneratorQProof.QDirection.up =
          siteEquiv parameters
            (moveSite site Direction.up)
        from moveSite_transport parameters site Direction.up]
      simp [configurationEquiv, updatedConfiguration, updatedSites]

theorem configurationEvents_transport (parameters : Parameters)
    (input : Configuration parameters) :
    (events input).map (eventEquiv parameters).toEmbedding =
      ProbabilityGeneratorQProof.configurationEvents
        (configurationEquiv parameters input) := by
  ext circuitEvent
  obtain ⟨event, rfl⟩ := (eventEquiv parameters).surjective circuitEvent
  rcases event with ⟨site, direction⟩
  cases direction <;>
    simp [events, ProbabilityGeneratorQProof.configurationEvents,
      configurationEquiv, eventEquiv]

theorem active_update_eq_transport (parameters : Parameters)
    (output input : Configuration parameters) (event : Event parameters)
    (active : event.1 ∈ input.1) :
    ProbabilityGeneratorQProof.updateConfiguration
          (configurationEquiv parameters input) (eventEquiv parameters event) =
        configurationEquiv parameters output ↔
      updatedSites input event = output.1 := by
  rw [active_event_transport parameters input event active]
  constructor
  · intro equal
    exact congrArg Subtype.val
      ((configurationEquiv parameters).injective equal)
  · intro equal
    apply congrArg (configurationEquiv parameters)
    exact Subtype.ext equal

theorem transitionCount_transport (parameters : Parameters)
    (output input : Configuration parameters) :
    transitionCount output input =
      ProbabilityGeneratorQProof.TechnicalReportQ.transitionCount
        ProbabilityGeneratorQProof.configurationEvents
        ProbabilityGeneratorQProof.updateConfiguration
        (configurationEquiv parameters output)
        (configurationEquiv parameters input) := by
  unfold transitionCount ProbabilityGeneratorQProof.TechnicalReportQ.transitionCount
  let sourceEvents := events input
  let sourceFiltered := sourceEvents.filter fun event =>
    updatedSites input event = output.1
  let targetFiltered :=
    (ProbabilityGeneratorQProof.configurationEvents
      (configurationEquiv parameters input)).filter fun event =>
        ProbabilityGeneratorQProof.updateConfiguration
          (configurationEquiv parameters input) event =
            configurationEquiv parameters output
  have mappedFiltered :
      sourceFiltered.map (eventEquiv parameters).toEmbedding = targetFiltered := by
    ext circuitEvent
    obtain ⟨event, rfl⟩ := (eventEquiv parameters).surjective circuitEvent
    have eventMembership :
        eventEquiv parameters event ∈
            ProbabilityGeneratorQProof.configurationEvents
              (configurationEquiv parameters input) ↔
          event ∈ sourceEvents := by
      constructor
      · intro targetMember
        have mappedMember : eventEquiv parameters event ∈
            (events input).map (eventEquiv parameters).toEmbedding := by
          rw [configurationEvents_transport parameters input]
          exact targetMember
        rcases Finset.mem_map.mp mappedMember with
          ⟨sourceEvent, sourceMember, mappedEqual⟩
        have sourceEqual : sourceEvent = event :=
          (eventEquiv parameters).injective mappedEqual
        subst sourceEvent
        exact sourceMember
      · intro sourceMember
        rw [← configurationEvents_transport parameters input]
        exact Finset.mem_map.mpr ⟨event, sourceMember, rfl⟩
    simp only [sourceFiltered, targetFiltered, Finset.mem_map,
      Finset.mem_filter]
    constructor
    · rintro ⟨sourceEvent, ⟨sourceMember, sourceUpdate⟩, mappedEqual⟩
      have sourceEventEqual : sourceEvent = event :=
        (eventEquiv parameters).injective mappedEqual
      subst sourceEvent
      have active : event.1 ∈ input.1 := by
        simpa [sourceEvents, events] using (Finset.mem_product.mp sourceMember).1
      exact ⟨eventMembership.mpr sourceMember,
        (active_update_eq_transport parameters output input event active).2
          sourceUpdate⟩
    · rintro ⟨targetMember, targetUpdate⟩
      have sourceMember : event ∈ sourceEvents := eventMembership.mp targetMember
      have active : event.1 ∈ input.1 := by
        simpa [sourceEvents, events] using (Finset.mem_product.mp sourceMember).1
      refine ⟨event, ⟨sourceMember, ?_⟩, rfl⟩
      exact (active_update_eq_transport parameters output input event active).1
        targetUpdate
  calc
    sourceFiltered.card =
        (sourceFiltered.map (eventEquiv parameters).toEmbedding).card := by simp
    _ = targetFiltered.card := congrArg Finset.card mappedFiltered

@[simp] theorem configurationParticleCount_transport (parameters : Parameters)
    (input : Configuration parameters) :
    ProbabilityGeneratorQProof.configurationParticleCount
        (configurationEquiv parameters input) = input.1.card := by
  simp [ProbabilityGeneratorQProof.configurationParticleCount, configurationEquiv]

/-- Every executable generator entry is the same independent generator entry
after the representation equivalence. -/
theorem generator_transport (parameters : Parameters)
    (output input : Configuration parameters) :
    (ProbabilityGeneratorQProof.configurationProbabilityGenerator
        (configurationEquiv parameters output)
        (configurationEquiv parameters input) : ℝ) =
      generator output input := by
  by_cases same : output = input
  · subst output
    simp [ProbabilityGeneratorQProof.configurationProbabilityGenerator,
      ProbabilityGeneratorQProof.TechnicalReportQ.probabilityGenerator,
      generator,
      configurationParticleCount_transport]
  · have transportedDifferent :
        configurationEquiv parameters output ≠
          configurationEquiv parameters input :=
      fun equal => same ((configurationEquiv parameters).injective equal)
    simp [ProbabilityGeneratorQProof.configurationProbabilityGenerator,
      ProbabilityGeneratorQProof.TechnicalReportQ.probabilityGenerator,
      generator, same, transportedDifferent,
      transitionCount_transport]

end

end QLean.Correspondence.GeneralRepresentationTransport
