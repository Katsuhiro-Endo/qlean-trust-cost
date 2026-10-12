import QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness

/-!
Representation-independent preparation facts for the shared finite builder.
Duplicate and omitted zero entries are interpreted by `SparseInitial.amplitude`.
No theorem here assumes or certifies an external QSP phase word.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteSparsePreparationTransport

open ProbabilityGeneratorQProof VerifiedCircuitCore
open QLean.Circuits.FiniteRationalConfigurationPreparation
open QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness
open QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness.SparseInitial

noncomputable section

private theorem deduplicated_nodup {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) : items.eraseDups.Nodup := by
  have go : ∀ n : Nat, ∀ values : List α,
      values.length = n → values.eraseDups.Nodup := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n inductionHypothesis =>
        intro values lengthEq
        cases values with
        | nil => simp
        | cons head tail =>
            rw [List.eraseDups_cons]
            apply List.nodup_cons.mpr
            constructor
            · intro member
              have inFiltered :
                  head ∈ tail.filter (fun value => !value == head) :=
                List.mem_eraseDups.mp member
              simp at inFiltered
            · have shorter :
                  (tail.filter (fun value => !value == head)).length < n := by
                have bound := List.length_filter_le
                  (fun value => !value == head) tail
                simp at lengthEq
                omega
              exact inductionHypothesis _ shorter _ rfl
  exact go items.length items rfl

theorem support_nodup {p : QParameters} (input : SparseInitial p) :
    input.support.Nodup := deduplicated_nodup _

theorem amplitude_zero_of_not_support {p : QParameters}
    (input : SparseInitial p) (configuration : QConfiguration p)
    (absent : configuration ∉ input.support) :
    input.amplitude configuration = 0 := by
  unfold SparseInitial.amplitude
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
  have different : entry.1 ≠ configuration := by
    intro same
    apply absent
    rw [SparseInitial.support, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨entry, entryMember, same⟩
  simp [different]

theorem branchMass_all {p : QParameters} (input : SparseInitial p)
    (depth pattern : Nat) :
    input.branchMass depth pattern =
      ∑ configuration : QConfiguration p,
        if matchesPrefix configuration depth pattern then
          (input.amplitude configuration) ^ 2 else 0 := by
  classical
  rw [SparseInitial.branchMass_eq_sum,
    ← List.sum_toFinset _ (support_nodup input)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro configuration _ absent
  have absentList : configuration ∉ input.support := by simpa using absent
  simp [amplitude_zero_of_not_support input configuration absentList]

/-- The sparse and complete presentations have the same branch masses;
their generated circuits need not be equal on unrelated inputs. -/
theorem branchMass_ofAmplitude_amplitude {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat) :
    (SparseInitial.ofAmplitude input.amplitude).branchMass depth pattern =
      input.branchMass depth pattern := by
  rw [branchMass_all, branchMass_all]
  simp only [SparseInitial.amplitude_ofAmplitude]

theorem branchMass_leaf {p : QParameters} (input : SparseInitial p)
    (configuration : QConfiguration p) :
    input.branchMass p.systemWidth (prefixPattern configuration p.systemWidth) =
      (input.amplitude configuration) ^ 2 := by
  rw [← branchMass_ofAmplitude_amplitude input,
    SparseInitial.branchMass_leaf_ofAmplitude]

theorem sign_on_configuration {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (clean : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (matched : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.support.filter fun candidate =>
              input.amplitude candidate < 0).map fun candidate =>
                Circuit.boolMultiControlledRy
                  ((branch, true) :: configurationControlsAt placement candidate)
                  placement.scratch placement.phase (.mul (rationalAngle 2) .pi)))
        state output =
      (if input.amplitude configuration < 0 then (-1 : ℂ) else 1) *
        state output := by
  rw [signAtWhen_applyOperator input placement branch facts
    state clean output]
  rw [signProduct_eq_if_mem placement branch configuration output matched _
    ((support_nodup input).filter _)]
  by_cases member : configuration ∈ input.support
  · simp [member]
  · simp [member, amplitude_zero_of_not_support input configuration member]

theorem circuit_on_configuration {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (clean : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (matched : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.circuitAtWhen placement branch)) state output =
      (if input.amplitude configuration < 0 then (-1 : ℂ) else 1) *
        applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (magnitudePrefixAtWhen input placement branch
              p.systemWidth)) state output := by
  unfold SparseInitial.circuitAtWhen
  simp only [Circuit.denote_seq, applyOperator_mul]
  simpa only [magnitudePrefixAtWhen_full,
    magnitudeLayerAtWhen] using
    sign_on_configuration input placement branch facts configuration _
      (magnitudeAtWhen_preserves_scratchZero input placement
        branch facts.toBranchPlacementFacts state clean) output matched

theorem afterHadamard_on_configuration {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < input.branchMass 0 0)
    (configuration : QConfiguration p) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.circuitAtWhen placement branch))
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (.gate (.h branch)))
          (basisKet (fun _ => false : QubitBasis qubits)))
        (prefixBasis placement branch facts.toBranchPlacementFacts
          p.systemWidth (prefixPattern configuration p.systemWidth)) =
      (if input.amplitude configuration < 0 then (-1 : ℂ) else 1) *
        (((1 / Real.sqrt 2 : ℝ) : ℂ) *
          (Real.sqrt
            (((input.amplitude configuration : ℚ) : ℝ) ^ 2 /
              ((input.branchMass 0 0 : ℚ) : ℝ)) : ℂ)) := by
  let zeroState : VerifiedCircuitCore.State (QubitBasis qubits) := basisKet (fun _ => false)
  have zeroScratch : SupportedOnScratchZero placement.scratch zeroState := by
    intro basis dirty
    obtain ⟨wire, _, trueAt⟩ := dirty
    have different : basis ≠ (fun _ => false : QubitBasis qubits) := by
      intro equal
      have atWire := congrFun equal wire
      simp [trueAt] at atWire
    simp [zeroState, basisKet_apply, different]
  have hadamardScratch := hadamard_preserves_scratchZero
    placement.scratch branch facts.branchOutsideScratch zeroState zeroScratch
  rw [circuit_on_configuration input placement branch facts configuration _
    hadamardScratch _
    (prefixBasis_configuration_controls placement branch
      facts.toBranchPlacementFacts configuration)]
  rw [magnitudeAfterHadamard_canonical_amplitude input placement
    branch facts.toBranchPlacementFacts rootPos
    (prefixPattern configuration p.systemWidth)
    (prefixPattern_lt configuration p.systemWidth), branchMass_leaf]
  push_cast
  rfl

theorem bPlusPreparation_on_configuration {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < input.branchMass 0 0)
    (configuration : QConfiguration p) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.bPlusPreparation placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits))
        (prefixBasis placement branch facts.toBranchPlacementFacts
          p.systemWidth (prefixPattern configuration p.systemWidth)) =
      (((1 / Real.sqrt 2 : ℝ) *
        ((input.amplitude configuration : ℝ) /
          Real.sqrt ((input.branchMass 0 0 : ℚ) : ℝ))) : ℂ) := by
  rw [SparseInitial.bPlusPreparation_circuit, Circuit.denote_seq,
    applyOperator_mul, afterHadamard_on_configuration
      input placement branch facts rootPos configuration]
  have rootPosReal : 0 < ((input.branchMass 0 0 : ℚ) : ℝ) := by
    exact_mod_cast rootPos
  have signIdentity := signed_sqrt_square_over_positive
    (input.amplitude configuration : ℝ)
    ((input.branchMass 0 0 : ℚ) : ℝ) rootPosReal
  have signTest : ((input.amplitude configuration : ℝ) < 0) ↔
      input.amplitude configuration < 0 := by norm_cast
  simp only [signTest] at signIdentity
  have scaled := congrArg (fun value : ℝ => (1 / Real.sqrt 2 : ℝ) * value)
    signIdentity
  calc
    _ = (((1 / Real.sqrt 2 : ℝ) *
          ((if input.amplitude configuration < 0 then (-1 : ℝ) else 1) *
            Real.sqrt (((input.amplitude configuration : ℝ) ^ 2) /
              ((input.branchMass 0 0 : ℚ) : ℝ)))) : ℂ) := by
          by_cases negative : input.amplitude configuration < 0 <;> simp [negative]
    _ = _ := by exact_mod_cast scaled

private theorem normalized_states_eq_on_saturated
    {basis : Type} [Fintype basis] [DecidableEq basis]
    (left right : VerifiedCircuitCore.State basis)
    (leftNormalized : IsNormalizedState left)
    (rightNormalized : IsNormalizedState right)
    (selected : Finset basis)
    (rightMass : (∑ index ∈ selected, Complex.normSq (right index)) = 1)
    (agree : ∀ index ∈ selected, left index = right index) : left = right := by
  have leftMass : (∑ index ∈ selected, Complex.normSq (left index)) = 1 := by
    calc
      _ = ∑ index ∈ selected, Complex.normSq (right index) := by
        apply Finset.sum_congr rfl
        intro index member
        rw [agree index member]
      _ = 1 := rightMass
  funext index
  by_cases member : index ∈ selected
  · exact agree index member
  · rw [normalized_state_zero_outside_saturated left leftNormalized
      selected leftMass index member,
      normalized_state_zero_outside_saturated right rightNormalized
        selected rightMass index member]

/-- Sparse lists, including duplicate entries and omitted zero entries,
prepare the same zero-input state as the complete amplitude presentation.
There is deliberately no equality of the two preparation unitaries. -/
theorem bPlusPreparation_zeroKet_eq_ofAmplitude
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < input.branchMass 0 0) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.bPlusPreparation placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits)) =
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude input.amplitude).bPlusPreparation
            placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits)) := by
  classical
  let output := applyOperator
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (input.bPlusPreparation placement branch).circuit)
    (basisKet (fun _ => false : QubitBasis qubits))
  let canonical := applyOperator
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      ((SparseInitial.ofAmplitude input.amplitude).bPlusPreparation
        placement branch).circuit)
    (basisKet (fun _ => false : QubitBasis qubits))
  let encode : QConfiguration p → QubitBasis qubits := fun configuration =>
    prefixBasis placement branch facts.toBranchPlacementFacts p.systemWidth
      (prefixPattern configuration p.systemWidth)
  let selected : Finset (QubitBasis qubits) :=
    insert (fun _ => false) (Finset.univ.image encode)
  have canonicalPos :
      0 < (SparseInitial.ofAmplitude input.amplitude).branchMass 0 0 := by
    simpa only [branchMass_ofAmplitude_amplitude] using rootPos
  have injective : Function.Injective encode :=
    configurationBasis_injective placement branch facts.toBranchPlacementFacts
  have zeroNotImage :
      (fun _ => false : QubitBasis qubits) ∉ Finset.univ.image encode := by
    intro member
    obtain ⟨configuration, _, equal⟩ := Finset.mem_image.mp member
    exact configurationBasis_ne_zero placement branch
      facts.toBranchPlacementFacts configuration equal
  have canonicalMass : (∑ basis ∈ selected, Complex.normSq (canonical basis)) = 1 := by
    rw [show selected = insert (fun _ => false) (Finset.univ.image encode) by rfl,
      Finset.sum_insert zeroNotImage,
      Finset.sum_image (fun left _ right _ equal => injective equal)]
    exact ofAmplitude_bPlusPreparation_selected_mass
      input.amplitude placement branch facts canonicalPos
  have atZero : output (fun _ => false) = canonical (fun _ => false) := by
    change applyOperator _ _ _ = applyOperator _ _ _
    rw [bPlusPreparation_zeroKet_false_branch_output input placement branch
      facts _ (by simp),
      bPlusPreparation_zeroKet_false_branch_output
        (SparseInitial.ofAmplitude input.amplitude) placement branch facts _ (by simp)]
  have atConfiguration (configuration : QConfiguration p) :
      output (encode configuration) = canonical (encode configuration) := by
    change applyOperator _ _ _ = applyOperator _ _ _
    rw [bPlusPreparation_on_configuration input placement branch facts rootPos,
      ofAmplitude_bPlusPreparation_on_configuration input.amplitude placement
        branch facts canonicalPos, branchMass_ofAmplitude_amplitude]
  apply normalized_states_eq_on_saturated output canonical
    (bPlusPreparation_zeroKet_normalized input placement branch)
    (bPlusPreparation_zeroKet_normalized
      (SparseInitial.ofAmplitude input.amplitude) placement branch)
    selected canonicalMass
  intro basis member
  obtain zero | image := Finset.mem_insert.mp member
  · simpa only [zero] using atZero
  · obtain ⟨configuration, _, equal⟩ := Finset.mem_image.mp image
    simpa only [← equal] using atConfiguration configuration

end
end QLean.Circuits.FiniteSparsePreparationTransport
