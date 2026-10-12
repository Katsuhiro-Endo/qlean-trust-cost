import QLean.Circuits.FiniteScientificCircuitSource
import QLean.Circuits.Foundation.ControlledCircuitCongruence
import QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness
import QLean.History.Implementation.HistoryPipelineFiniteScientificP05Bridge
import QLean.Circuits.Foundation.UniformPreparationFullOperatorCorrectness
import QLean.SignalProcessing.NativeSignalQSVTGeneric
import QLean.SignalProcessing.NativeSingularPairTwoFrame
import QLean.SignalProcessing.NativeConcreteP18QSPWitness
import QLean.SignalProcessing.M13bFiniteOuterCompiler

/-! Independent history RHS normalization and bPlus entries for the approved theoretical initial input. This does not certify numerical-provider output. -/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteScientificPreparationBridge

open JenningsHistory

theorem rhsNormSq_eq_initial_mass
    {d c r m R : Nat} (system : HistorySpec d c r m R) :
    rhsNormSq system =
      ∑ state : Fin d, system.initial state * system.initial state := by
  classical
  have decompose (f : HistoryIndex d c R → ℝ) :
      (∑ index, f index) =
        ∑ clock, ∑ order, ∑ state,
          f (HistoryIndex.proxyTypeEquiv d c R ⟨clock, order, state⟩) := by
    calc
      (∑ index, f index) =
          ∑ tuple : (Σ clock : Fin c, Σ order : Fin R, Fin d),
            f (HistoryIndex.proxyTypeEquiv d c R tuple) := by
        symm
        exact Fintype.sum_equiv (HistoryIndex.proxyTypeEquiv d c R)
          (fun tuple => f (HistoryIndex.proxyTypeEquiv d c R tuple)) f
          (by intro tuple; rfl)
      _ = _ := by simp only [Fintype.sum_sigma]
  unfold rhsNormSq
  rw [decompose]
  have clockPositive : 0 < c :=
    lt_trans system.physical_pos system.physical_lt
  have orderPositive : 0 < R :=
    lt_of_le_of_lt (Nat.zero_le r) system.order_lt
  let zeroClock : Fin c := ⟨0, clockPositive⟩
  let zeroOrder : Fin R := ⟨0, orderPositive⟩
  have clock_eq (clock : Fin c) :
      (clock.val = 0) ↔ clock = zeroClock := by
    constructor
    · intro equal
      apply Fin.ext
      exact equal
    · intro equal
      exact congrArg Fin.val equal
  have order_eq (order : Fin R) :
      (order.val = 0) ↔ order = zeroOrder := by
    constructor
    · intro equal
      apply Fin.ext
      exact equal
    · intro equal
      exact congrArg Fin.val equal
  dsimp [historyRhs, HistoryIndex.proxyTypeEquiv]
  let mass : ℝ :=
    ∑ state : Fin d, system.initial state * system.initial state
  have perClock (clock : Fin c) :
      (∑ order : Fin R,
        ∑ state : Fin d,
          (if clock.val = 0 ∧ order.val = 0 then
            system.initial state else 0) *
          (if clock.val = 0 ∧ order.val = 0 then
            system.initial state else 0)) =
        if clock = zeroClock then mass else 0 := by
    by_cases equal : clock = zeroClock
    · subst clock
      simp [zeroClock, mass, order_eq, zeroOrder]
    · have nonzero : clock.val ≠ 0 :=
        (clock_eq clock).not.mpr equal
      simp [nonzero, equal]
  calc
    _ = ∑ clock : Fin c, if clock = zeroClock then mass else 0 := by
      apply Finset.sum_congr rfl
      intro clock _
      exact perClock clock
    _ = mass := by simp
    _ = _ := rfl

end QLean.Circuits.FiniteScientificPreparationBridge

namespace QLean.Circuits.FiniteScientificPreparationBridge

open ExecutableHistoryExecutableP18
open ExecutableHistoryExecutableHistory
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryReferenceM10Bridge
open ExecutableHistoryCore
open QLean.Circuits.FiniteRationalConfigurationPreparation
open QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness
open QLean.Circuits.FiniteScientificCircuitSource
open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryImplementationRole

theorem executable_rhsNormSq_eq_sparse_root
    (source : AlignedCommonSource119) :
    JenningsHistory.rhsNormSq (executableSystem119 source) =
      (((SparseInitial.ofAmplitude source.initial).branchMass 0 0 : ℚ) : ℝ) := by
  classical
  rw [rhsNormSq_eq_initial_mass]
  rw [SparseInitial.branchMass_root_ofAmplitude]
  let equivalence :=
    configurationEquiv (ProbabilityGeneratorQProof.QConfiguration source.qParameters)
  have sumEquiv :
      (∑ configuration : ProbabilityGeneratorQProof.QConfiguration source.qParameters,
        (source.initial configuration : ℝ) *
          (source.initial configuration : ℝ)) =
      ∑ state : Fin (Fintype.card
          (ProbabilityGeneratorQProof.QConfiguration source.qParameters)),
        (source.initial (equivalence.symm state) : ℝ) *
          (source.initial (equivalence.symm state) : ℝ) := by
    exact Fintype.sum_equiv equivalence _ _
      (by intro configuration; simp [equivalence])
  convert sumEquiv.symm using 1 <;>
    simp [executableSystem119, translatedSystem,
      configurationEquiv, equivalence, pow_two]

theorem executable_rhsNorm_eq_sparse_root
    (source : AlignedCommonSource119) :
    JenningsHistory.rhsNorm (executableSystem119 source) =
      Real.sqrt
        (((SparseInitial.ofAmplitude source.initial).branchMass 0 0 : ℚ) : ℝ) := by
  rw [JenningsHistory.rhsNorm, executable_rhsNormSq_eq_sparse_root]

theorem executable_bPlus_history_entry
    (source : AlignedCommonSource119)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    JenningsHistory.dalzellBPlus (executableSystem119 source) (Sum.inl row) =
      (if row.clock.val = 0 ∧ row.order.val = 0 then
        (source.initial
          ((configurationEquiv
            (ProbabilityGeneratorQProof.QConfiguration source.qParameters)).symm
              row.state) : ℝ)
      else 0) /
        Real.sqrt
          (((SparseInitial.ofAmplitude source.initial).branchMass 0 0 : ℚ) : ℝ) /
        Real.sqrt 2 := by
  simp only [JenningsHistory.dalzellBPlus,
    JenningsHistory.normalizedRhs]
  rw [executable_rhsNorm_eq_sparse_root]
  simp [JenningsHistory.historyRhs, executableSystem119,
    translatedSystem, configurationEquiv]

theorem executable_bPlus_extension_entry
    (source : AlignedCommonSource119) :
    JenningsHistory.dalzellBPlus (executableSystem119 source)
      (Sum.inr ()) = 1 / Real.sqrt 2 := rfl

/-- The nonzero approved scientific initial input supplies the root-mass
precondition required by the common finite bPlus preparer. -/
theorem executable_sparse_root_pos
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    0 < (SparseInitial.ofAmplitude source.initial).branchMass 0 0 := by
  classical
  by_contra notPositive
  have allZero : ∀ configuration, source.initial configuration = 0 := by
    intro configuration
    by_contra nonzero
    exact notPositive
      (SparseInitial.branchMass_root_pos_ofAmplitude
        source.initial configuration nonzero)
  have initialZero : source.initial = 0 := by
    funext configuration
    exact allZero configuration
  exact assumptions.sourceInitial_nonzero initialZero

private theorem prepWidth023_eq_three (width : Nat) :
    prepWidth023 width = 3 * width := by
  rw [prepWidth023_eq_data_plus_work]
  simp only [prepWorkCount023]
  omega

private theorem dataPlacement023_val_three (width : Nat)
    (wire : Fin width) :
    (dataPlacement023 width wire).val = 3 * wire.val := by
  induction width with
  | zero => exact Fin.elim0 wire
  | succ width inductionHypothesis =>
      by_cases below : wire.val < width
      · change (if h : wire.val < width then
            (⟨(dataPlacement023 width ⟨wire.val, h⟩).val, by
              have limit := (dataPlacement023 width ⟨wire.val, h⟩).isLt
              rw [prepWidth023]
              omega⟩ : Fin (prepWidth023 (width + 1)))
          else ⟨prepWidth023 width, by
            rw [prepWidth023]
            omega⟩).val = 3 * wire.val
        rw [dif_pos below]
        exact inductionHypothesis ⟨wire.val, below⟩
      · have last : wire.val = width := by omega
        simp [dataPlacement023, last, prepWidth023_eq_three]

private theorem finite_rhs_data_val (input : FiniteScientificSource)
    (bit : Fin input.qParameters.systemWidth) :
    (input.rhsPlacement.data bit).val =
      3 * (finiteScientificHistoryDataWire119 input.layoutSource bit).val := by
  change (dataPlacement023 input.branchQubits
    (lowerPlacement119 input.historyQubits
      (finiteScientificHistoryDataWire119 input.layoutSource bit))).val = _
  rw [dataPlacement023_val_three]
  rfl

private theorem finite_rhs_branch_val (input : FiniteScientificSource) :
    input.historyControlLayout.control.val =
      3 * input.historyQubits := by
  change (dataPlacement023 input.branchQubits
    (topControl119 input.historyQubits)).val = _
  rw [dataPlacement023_val_three]
  rfl

private theorem finite_systemWidth_le_historyQubits
    (input : FiniteScientificSource) :
    input.qParameters.systemWidth ≤ input.historyQubits := by
  dsimp [FiniteScientificSource.historyQubits,
    finiteScientificHistoryQubits119,
    FiniteScientificSource.layoutSource]
  omega

private theorem finite_rhs_scratch_member_val
    (input : FiniteScientificSource)
    (wire : Fin input.preparationQubits)
    (member : wire ∈ input.rhsPlacement.scratch) :
    ∃ bit : Fin input.qParameters.systemWidth,
      wire.val = 3 * bit.val + 1 := by
  simp only [FiniteScientificSource.rhsPlacement, List.mem_map] at member
  rcases member with ⟨bit, _, rfl⟩
  exact ⟨bit, rfl⟩

private def finite_rhs_scratch_wire (input : FiniteScientificSource)
    (bit : Fin input.qParameters.systemWidth) :
    Fin input.preparationQubits :=
  ⟨3 * bit.val + 1, by
    rw [FiniteScientificSource.preparationQubits,
      prepWidth023_eq_three]
    have bound := bit.isLt
    have widthBound := finite_systemWidth_le_historyQubits input
    dsimp [FiniteScientificSource.branchQubits]
    omega⟩

private theorem finite_rhs_scratch_eq_map (input : FiniteScientificSource) :
    input.rhsPlacement.scratch =
      (List.finRange input.qParameters.systemWidth).map
        (finite_rhs_scratch_wire input) := by
  rfl

private theorem finite_rhs_scratch_wire_injective
    (input : FiniteScientificSource) :
    Function.Injective (finite_rhs_scratch_wire input) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [finite_rhs_scratch_wire] at values
  omega

private theorem finite_rhs_scratch_nodup
    (input : FiniteScientificSource) :
    input.rhsPlacement.scratch.Nodup := by
  rw [finite_rhs_scratch_eq_map]
  exact List.Nodup.map (finite_rhs_scratch_wire_injective input)
    (List.nodup_finRange input.qParameters.systemWidth)

/-- The finite scientific preparer uses disjoint data, scratch, branch and
sign wires for every admitted scientific shape. This is a wire fact, not a
claim of accuracy for a numerical phase provider. -/
theorem finite_rhs_sign_facts (input : FiniteScientificSource) :
    SignPlacementFacts input.rhsPlacement
      input.historyControlLayout.control := by
  refine {
    dataInjective := ?_
    scratchNodup := finite_rhs_scratch_nodup input
    dataOutsideScratch := ?_
    scratchLength := ?_
    branchOutsideData := ?_
    branchOutsideScratch := ?_
    phaseOutsideData := ?_
    phaseOutsideScratch := ?_
    phaseOutsideBranch := ?_ }
  · intro left right equal
    apply finiteScientificHistoryDataWire119_injective input.layoutSource
    apply input.historyControlLayout.placement.injective
    exact equal
  · intro bit member
    obtain ⟨scratchBit, scratchValue⟩ :=
      finite_rhs_scratch_member_val input _ member
    have dataValue := finite_rhs_data_val input bit
    omega
  · rw [finite_rhs_scratch_eq_map, List.length_map,
      List.length_finRange]
  · intro bit equal
    have branchValue := finite_rhs_branch_val input
    have dataValue := finite_rhs_data_val input bit
    have dataBound :=
      (finiteScientificHistoryDataWire119 input.layoutSource bit).isLt
    change (finiteScientificHistoryDataWire119 input.layoutSource bit).val <
      input.historyQubits at dataBound
    have values := congrArg Fin.val equal
    omega

  · intro member
    obtain ⟨scratchBit, scratchValue⟩ :=
      finite_rhs_scratch_member_val input _ member
    have branchValue := finite_rhs_branch_val input
    have widthBound := finite_systemWidth_le_historyQubits input
    have scratchBound := scratchBit.isLt
    omega
  · intro bit equal
    have dataValue := finite_rhs_data_val input bit
    have phaseValue : input.rhsPlacement.phase.val =
        3 * input.qParameters.systemWidth + 1 := rfl
    have values := congrArg Fin.val equal
    omega
  · intro member
    obtain ⟨scratchBit, scratchValue⟩ :=
      finite_rhs_scratch_member_val input _ member
    have phaseValue : input.rhsPlacement.phase.val =
        3 * input.qParameters.systemWidth + 1 := rfl
    have scratchBound := scratchBit.isLt
    omega
  · intro equal
    have branchValue := finite_rhs_branch_val input
    have phaseValue : input.rhsPlacement.phase.val =
        3 * input.qParameters.systemWidth + 1 := rfl
    have values := congrArg Fin.val equal
    omega

/-- The same finite scientific constructor, when instantiated with the
approved theoretical initial input, prepares its independently defined
encoded bPlus target on every physical basis. No arbitrary numerical
provider receives this theorem. -/
theorem theoretical_rhsPreparation_eq_encodedBPlus
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    VerifiedCircuitCore.applyOperator
        (VerifiedCircuitCore.Circuit.denote
          (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
          input.rhsPreparation.circuit)
        (VerifiedCircuitCore.basisKet
          (fun _ => false : VerifiedCircuitCore.QubitBasis
            input.preparationQubits)) =
      encodedBPlusTarget source.initial input.rhsPlacement
        input.historyControlLayout.control (finite_rhs_sign_facts input) := by
  dsimp [FiniteScientificSource.ofAlignedCommonSource,
    FiniteScientificSource.rhsPreparation]
  exact SparseInitial.ofAmplitude_bPlusPreparation_eq_encodedBPlusTarget
    source.initial _ _ (finite_rhs_sign_facts _)
    (executable_sparse_root_pos source assumptions)

/-- The approved P18 ideal vector has the same normalized history entries
as the common preparer's independent encoded target. The physical embedding
comparison is still a separate obligation. -/
theorem executable_p18BPlus_history_entry
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    p18BPlus119 (executableP18Input119 source assumptions) (Sum.inl row) =
      (if row.clock.val = 0 ∧ row.order.val = 0 then
        (source.initial
          ((configurationEquiv
            (ProbabilityGeneratorQProof.QConfiguration source.qParameters)).symm
              row.state) : ℝ)
      else 0) /
        Real.sqrt
          (((SparseInitial.ofAmplitude source.initial).branchMass 0 0 : ℚ) : ℝ) /
        Real.sqrt 2 := by
  rw [p18BPlus119_eq_dalzell]
  exact executable_bPlus_history_entry source row

theorem executable_p18BPlus_extension_entry
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    p18BPlus119 (executableP18Input119 source assumptions)
      (Sum.inr ()) = 1 / Real.sqrt 2 := by
  rw [p18BPlus119_eq_dalzell]
  exact executable_bPlus_extension_entry source

/-- The independent history index with clock and order zero for a named
configuration. Its finite state number follows the approved mathematical
equivalence, not the numerical emitter's bitmask enumeration. -/
noncomputable def initialHistoryRow
    (source : AlignedCommonSource119)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) where
  clock := ⟨0, lt_trans (executableSystem119 source).physical_pos
    (executableSystem119 source).physical_lt⟩
  order := ⟨0, lt_of_le_of_lt (Nat.zero_le _)
    (executableSystem119 source).order_lt⟩
  state := configurationEquiv _ configuration

/-- The finite history emitter numbers configurations by its explicit
enumeration. The theoretical history vector uses the legacy `Fintype` index;
the two are related by the already proved permutation, not by definition. -/
def canonicalInitialHistoryRow
    (source : AlignedCommonSource119)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) where
  clock := ⟨0, lt_trans (executableSystem119 source).physical_pos
    (executableSystem119 source).physical_lt⟩
  order := ⟨0, lt_of_le_of_lt (Nat.zero_le _)
    (executableSystem119 source).order_lt⟩
  state := ProbabilityGeneratorQProof.configurationEquivCard
    source.qParameters configuration

theorem canonicalInitialHistoryRow_legacy
    (source : AlignedCommonSource119)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    legacyHistoryIndexOfCanonical119 source
        (canonicalInitialHistoryRow source configuration) =
      initialHistoryRow source configuration := by
  simp [legacyHistoryIndexOfCanonical119, canonicalInitialHistoryRow,
    initialHistoryRow, ProbabilityGeneratorQProof.canonicalToLegacyIndex,
    ExecutableHistoryReferenceM10Bridge.configurationEquiv]

private theorem finite_write_zero
    {qubits width : Nat} (register : VerifiedCircuitCore.Register qubits width) :
    VerifiedCircuitCore.writeRegisterBitsFinite register (fun _ => false)
      (fun _ => false) = (fun _ => false) := by
  funext wire
  simp only [VerifiedCircuitCore.writeRegisterBitsFinite]
  split <;> rfl

private theorem little_endian_zero (qubits : Nat) :
    VerifiedCircuitCore.qubitBasisOfLittleEndianIndex
        (0 : Fin (2 ^ qubits)) = (fun _ => false) := by
  funext wire
  simp [VerifiedCircuitCore.qubitBasisOfLittleEndianIndex]

theorem canonicalInitialHistoryBasis_data_only
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    finiteScientificCanonicalHistoryBasis119 source fits
        (canonicalInitialHistoryRow source configuration) =
      VerifiedCircuitCore.writeRegisterBitsFinite
        (finiteScientificHistoryDataRegister119 source)
        (ProbabilityGeneratorQProof.delimiterEncoding configuration)
        (fun _ => false) := by
  simp [finiteScientificCanonicalHistoryBasis119,
    canonicalOldHistoryIndex119, canonicalInitialHistoryRow,
    finiteHistoryBasisAtRegisters, clockBits119, orderBits119,
    little_endian_zero]
  have hOrder := finite_write_zero
    (finiteScientificHistoryOrderRegister119 source)
  have hClock :
      VerifiedCircuitCore.writeRegisterBitsFinite
          (finiteScientificHistoryClockRegister119 source) (fun _ => false)
          (VerifiedCircuitCore.writeRegisterBitsFinite
            (finiteScientificHistoryOrderRegister119 source) (fun _ => false)
            (fun _ => false)) = (fun _ => false) := by
    rw [hOrder]
    exact finite_write_zero _
  exact congrArg
    (fun basis => VerifiedCircuitCore.writeRegisterBitsFinite
      (finiteScientificHistoryDataRegister119 source)
      (fun bit => ProbabilityGeneratorQProof.delimiterEncoding configuration bit)
      basis) hClock

/-- Every finite canonical history word is the established theoretical
physical history word after the explicit width cast and proof-only change
from canonical configuration numbering to legacy numbering. -/
theorem finiteHistoryBasis_to_executableEmbedding
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source))
    (wire : Fin (ExecutableRaw119 source).history.qubits) :
    finiteScientificCanonicalHistoryBasis119 source fits row
        (Fin.cast (finiteScientificHistoryQubits119_eq source).symm wire) =
      executableP18HistoryEmbedding119 source domain fits
        (legacyHistoryIndexOfCanonical119 source row) wire := by
  rw [finiteScientificCanonicalHistoryBasis119_scientific_eq
    source domain fits row wire]
  exact congrFun
    (canonicalHistoryPhysicalBasis119_reindexed source domain fits row) wire

private theorem finiteScientificCanonicalHistoryBasis_injective
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    Function.Injective
      (finiteScientificCanonicalHistoryBasis119 source fits) := by
  intro left right equal
  have physicalEqual :
      canonicalHistoryPhysicalBasis119 source domain fits left =
        canonicalHistoryPhysicalBasis119 source domain fits right := by
    funext wire
    have atWire := congrFun equal
      (Fin.cast (finiteScientificHistoryQubits119_eq source).symm wire)
    rw [finiteScientificCanonicalHistoryBasis119_scientific_eq
      source domain fits left wire,
      finiteScientificCanonicalHistoryBasis119_scientific_eq
        source domain fits right wire] at atWire
    exact atWire
  rw [canonicalHistoryPhysicalBasis119_reindexed,
    canonicalHistoryPhysicalBasis119_reindexed] at physicalEqual
  have legacyEqual :=
    (executableP18HistoryEmbedding119 source domain fits).injective physicalEqual
  cases left with
  | mk leftClock leftOrder leftState =>
    cases right with
    | mk rightClock rightOrder rightState =>
      simp only [legacyHistoryIndexOfCanonical119,
        JenningsHistory.HistoryIndex.mk.injEq] at legacyEqual ⊢
      rcases legacyEqual with ⟨clockEqual, orderEqual, stateEqual⟩
      exact ⟨clockEqual, orderEqual,
        (ProbabilityGeneratorQProof.canonicalToLegacyIndex
          source.qParameters).injective stateEqual⟩

private theorem finite_merge_comp
    {a b c : Nat} (first : Fin a ↪ Fin b) (second : Fin b ↪ Fin c)
    (inside : VerifiedCircuitCore.QubitBasis a)
    (middle : VerifiedCircuitCore.QubitBasis b)
    (outside : VerifiedCircuitCore.QubitBasis c) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis second
        (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis first inside middle)
        outside =
      VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis (first.trans second)
        inside
        (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis second middle outside) := by
  classical
  funext wire
  simp only [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq,
    VerifiedCircuitCore.mergePlacedAndOutsideBasis]
  by_cases hqp : ∃ source, second (first source) = wire
  · have hq : ∃ source, second source = wire :=
      ⟨first (Classical.choose hqp), Classical.choose_spec hqp⟩
    have hfirst : ∃ source, first source = Classical.choose hq := by
      refine ⟨Classical.choose hqp, ?_⟩
      exact second.injective
        ((Classical.choose_spec hqp).trans (Classical.choose_spec hq).symm)
    have hchoice : Classical.choose hfirst = Classical.choose hqp := by
      apply (first.trans second).injective
      calc
        second (first (Classical.choose hfirst)) =
            second (Classical.choose hq) := by
          rw [Classical.choose_spec hfirst]
        _ = wire := Classical.choose_spec hq
        _ = second (first (Classical.choose hqp)) :=
          (Classical.choose_spec hqp).symm
    simp [hq, hqp, hfirst, hchoice]
  · by_cases hq : ∃ source, second source = wire
    · have hfirst : ¬ ∃ source, first source = Classical.choose hq := by
        intro ⟨source, equal⟩
        exact hqp ⟨source, by
          rw [equal]
          exact Classical.choose_spec hq⟩
      simp [hq, hqp, hfirst]
    · have hqpFalse : ¬ ∃ source, second (first source) = wire := by
        intro ⟨source, equal⟩
        exact hq ⟨first source, equal⟩
      simp [hq, hqpFalse]

private theorem finite_merge_zero_control
    {a b : Nat} (placement : Fin a ↪ Fin b) (control : Fin b)
    (outside : ∀ source, placement source ≠ control) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis placement
        (fun _ => false) (fun wire => if wire = control then true else false) =
      (fun wire => if wire = control then true else false) := by
  classical
  rw [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq]
  funext wire
  by_cases atControl : wire = control
  · subst wire
    have missing : ¬ ∃ source, placement source = control := by
      intro ⟨source, equal⟩
      exact outside source equal
    simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis, missing]
  · by_cases inImage : ∃ source, placement source = wire
    · simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis,
        inImage, atControl]
    · simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis,
        inImage, atControl]

private theorem finite_merge_all_zero
    {a b : Nat} (placement : Fin a ↪ Fin b) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis placement
        (fun _ => false) (fun _ => false) =
      (fun _ => false) := by
  classical
  rw [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq]
  funext wire
  simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis]

private theorem finite_merge_at_placed
    {a b : Nat} (placement : Fin a ↪ Fin b)
    (internal : VerifiedCircuitCore.QubitBasis a)
    (outside : VerifiedCircuitCore.QubitBasis b) (source : Fin a) :
    (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis placement
      internal outside) (placement source) = internal source := by
  rw [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq]
  exact congrFun
    (VerifiedCircuitCore.restrictToPlacedWires_mergePlacedAndOutsideBasis
      placement internal (fun wire => outside wire.1)) source

private theorem finite_merge_at_outside
    {a b : Nat} (placement : Fin a ↪ Fin b)
    (internal : VerifiedCircuitCore.QubitBasis a)
    (outside : VerifiedCircuitCore.QubitBasis b) (wire : Fin b)
    (notPlaced : ∀ source, placement source ≠ wire) :
    (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis placement
      internal outside) wire = outside wire := by
  rw [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq]
  let outsideWire : VerifiedCircuitCore.OutsideWire placement :=
    ⟨wire, notPlaced⟩
  exact congrFun
    (VerifiedCircuitCore.restrictToOutsideWires_mergePlacedAndOutsideBasis
      placement internal (fun other => outside other.1)) outsideWire

private theorem finite_merge_control_zero
    {a b : Nat} (placement : Fin a ↪ Fin b) (control : Fin a) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis placement
        (fun wire => if wire = control then true else false)
        (fun _ => false) =
      (fun wire => if wire = placement control then true else false) := by
  classical
  rw [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq]
  funext wire
  by_cases inImage : ∃ source, placement source = wire
  · obtain ⟨source, rfl⟩ := inImage
    by_cases atControl : source = control
    · subst source
      simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis]
    · have notControl : placement source ≠ placement control := by
        intro equal
        exact atControl (placement.injective equal)
      simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis,
        atControl, notControl]
  · have notControl : wire ≠ placement control := by
      intro equal
      exact inImage ⟨control, equal.symm⟩
    simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis,
      inImage, notControl]

private theorem finite_branch_data_composed
    {a b c d : Nat}
    (historyData : Fin a ↪ Fin b) (branch : Fin b ↪ Fin c)
    (outer : Fin c ↪ Fin d) (control : Fin c)
    (controlOutside : ∀ wire, branch wire ≠ control)
    (configurationBits : VerifiedCircuitCore.QubitBasis a) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis outer
        (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis branch
          (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis historyData
            configurationBits (fun _ => false))
          (fun wire => if wire = control then true else false))
        (fun _ => false) =
      VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        ((historyData.trans branch).trans outer) configurationBits
        (fun wire => if wire = outer control then true else false) := by
  rw [finite_merge_comp historyData branch]
  rw [finite_merge_zero_control branch control controlOutside]
  rw [finite_merge_comp (historyData.trans branch) outer]
  rw [finite_merge_control_zero outer control]

def scientificHistoryDataEmbedding
    (input : FiniteScientificSource) :
    Fin input.qParameters.systemWidth ↪ Fin input.historyQubits where
  toFun := finiteScientificHistoryDataWire119 input.layoutSource
  inj' := finiteScientificHistoryDataWire119_injective input.layoutSource

theorem scientificHistoryDataEmbedding_composed
    (input : FiniteScientificSource) :
    ∀ bit,
      (((scientificHistoryDataEmbedding input).trans
        input.branchLayout.placement).trans
        (dataPlacement023 input.branchQubits)) bit =
      input.rhsPlacement.data bit := by
  intro bit
  rfl

theorem scientificBranchControl_composed
    (input : FiniteScientificSource) :
    dataPlacement023 input.branchQubits input.branchLayout.control =
      input.historyControlLayout.control := rfl

theorem canonicalInitialHistoryBasis_finiteMerge
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      input.qParameters) :
    finiteScientificCanonicalHistoryBasis119 input.layoutSource fits
        (canonicalInitialHistoryRow input.layoutSource configuration) =
      VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        (scientificHistoryDataEmbedding input)
        (ProbabilityGeneratorQProof.delimiterEncoding configuration)
        (fun _ => false) := by
  rw [canonicalInitialHistoryBasis_data_only]
  rfl

/-- Internal layout identity for the shared preparation builder. It is used
when that builder is instantiated by the theoretical scientific input; it does
not certify a circuit emitted with a numerical phase provider. -/
private theorem scientificInitialPhysicalBasis_finiteMerge
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      input.qParameters) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        (dataPlacement023 input.branchQubits)
        (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
          input.branchLayout.placement
          (finiteScientificCanonicalHistoryBasis119 input.layoutSource fits
            (canonicalInitialHistoryRow input.layoutSource configuration))
          (fun wire => if wire = input.branchLayout.control then true else false))
        (fun _ => false) =
      VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        ⟨input.rhsPlacement.data,
          (finite_rhs_sign_facts input).dataInjective⟩
        (ProbabilityGeneratorQProof.delimiterEncoding configuration)
        (fun wire => if wire = input.historyControlLayout.control then true
          else false) := by
  rw [canonicalInitialHistoryBasis_finiteMerge]
  have placementEq :
      (((scientificHistoryDataEmbedding input).trans
        input.branchLayout.placement).trans
        (dataPlacement023 input.branchQubits)) =
      (⟨input.rhsPlacement.data,
        (finite_rhs_sign_facts input).dataInjective⟩ :
        Fin input.qParameters.systemWidth ↪
          Fin input.preparationQubits) := by
    apply Function.Embedding.ext
    intro bit
    exact scientificHistoryDataEmbedding_composed input bit
  refine (finite_branch_data_composed
      (scientificHistoryDataEmbedding input) input.branchLayout.placement
      (dataPlacement023 input.branchQubits) input.branchLayout.control
      (by
        intro wire
        exact Ne.symm (input.branchLayout.control_ne_placed wire))
      (ProbabilityGeneratorQProof.delimiterEncoding configuration)).trans ?_
  rw [placementEq, scientificBranchControl_composed]
  congr 1

/-- The nested physical label of the common preparer is the independent
encoded label when the builder is instantiated by the theoretical input.
This is a layout identity, not a guarantee for numerical-provider output. -/
private theorem scientificInitialPhysicalBasis_eq_encodedBPlusBasis
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      input.qParameters) :
    VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        (dataPlacement023 input.branchQubits)
        (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
          input.branchLayout.placement
          (finiteScientificCanonicalHistoryBasis119 input.layoutSource fits
            (canonicalInitialHistoryRow input.layoutSource configuration))
          (fun wire => if wire = input.branchLayout.control then true else false))
        (fun _ => false) =
      encodedBPlusConfigurationBasis input.rhsPlacement
        input.historyControlLayout.control (finite_rhs_sign_facts input)
        configuration := by
  rw [scientificInitialPhysicalBasis_finiteMerge]
  rw [VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis_eq]
  rfl

/-- The finite H-history plan and the shared preparation target use the same
physical label. This is kept internal until the theoretical source is bound. -/
private theorem scientificInitialPlanBasis_eq_encodedBPlusBasis
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      input.qParameters) :
    VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
        (dataPlacement023 input.branchQubits) (fun _ => false)
        (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
          (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
            input.layoutSource fits input.branchLayout)
          (Sum.inl (canonicalInitialHistoryRow input.layoutSource configuration))) =
      encodedBPlusConfigurationBasis input.rhsPlacement
        input.historyControlLayout.control (finite_rhs_sign_facts input)
        configuration := by
  exact scientificInitialPhysicalBasis_eq_encodedBPlusBasis input fits
    configuration

private theorem scientificExtensionPlanBasis_zero
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource) :
    VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
        (dataPlacement023 input.branchQubits) (fun _ => false)
        (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
          (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
            input.layoutSource fits input.branchLayout)
          (Sum.inr ())) =
      (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits) := by
  change VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
      (dataPlacement023 input.branchQubits)
      (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        input.branchLayout.placement (fun _ => false)
        (fun wire => if wire = input.branchLayout.control then false else false))
      (fun _ => false) = (fun _ => false)
  simp only [ite_self, finite_merge_all_zero]

private theorem scientificHistoryPlanBasis_control_true
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 input.layoutSource)
      (ExecutableC119 input.layoutSource)
      (ExecutableLabels119 input.layoutSource)) :
    (VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
        (dataPlacement023 input.branchQubits) (fun _ => false)
        (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
          (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
            input.layoutSource fits input.branchLayout)
          (Sum.inl row))) input.historyControlLayout.control = true := by
  change (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
      (dataPlacement023 input.branchQubits)
      (VerifiedCircuitCore.finiteMergePlacedAndOutsideBasis
        input.branchLayout.placement
        (finiteScientificCanonicalHistoryBasis119 input.layoutSource fits row)
        (fun wire => if wire = input.branchLayout.control then true else false))
      (fun _ => false))
        ((dataPlacement023 input.branchQubits) input.branchLayout.control) = true
  rw [finite_merge_at_placed]
  rw [finite_merge_at_outside input.branchLayout.placement
    (finiteScientificCanonicalHistoryBasis119 input.layoutSource fits row)
    (fun wire => if wire = input.branchLayout.control then true else false)
    input.branchLayout.control
    (by
      intro wire
      exact Ne.symm (input.branchLayout.control_ne_placed wire))]
  simp

private theorem scientificHistoryPlanBasis_ne_zero
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 input.layoutSource)
      (ExecutableC119 input.layoutSource)
      (ExecutableLabels119 input.layoutSource)) :
    VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
        (dataPlacement023 input.branchQubits) (fun _ => false)
        (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
          (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
            input.layoutSource fits input.branchLayout)
          (Sum.inl row)) ≠
      (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits) := by
  intro equal
  have atControl := congrFun equal input.historyControlLayout.control
  rw [scientificHistoryPlanBasis_control_true input fits row] at atControl
  simp at atControl

/-- At every prepared configuration basis, the independent encoded target
has exactly the corresponding independent P18 bPlus amplitude. -/
theorem encodedBPlusTarget_eq_p18BPlus_at_configuration
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    encodedBPlusTarget source.initial input.rhsPlacement
        input.historyControlLayout.control (finite_rhs_sign_facts input)
        (encodedBPlusConfigurationBasis input.rhsPlacement
          input.historyControlLayout.control (finite_rhs_sign_facts input)
          configuration) =
      ((p18BPlus119 (executableP18Input119 source assumptions)
        (Sum.inl (initialHistoryRow source configuration)) : ℝ) : ℂ) := by
  dsimp only [FiniteScientificSource.ofAlignedCommonSource]
  rw [encodedBPlusTarget_on_configuration source.initial _ _
    (finite_rhs_sign_facts _) (executable_sparse_root_pos source assumptions)]
  rw [executable_p18BPlus_history_entry]
  simp [initialHistoryRow, configurationEquiv]
  ring

theorem encodedBPlusTarget_eq_p18BPlus_at_extension
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    encodedBPlusTarget source.initial input.rhsPlacement
        input.historyControlLayout.control (finite_rhs_sign_facts input)
        (fun _ => false : VerifiedCircuitCore.QubitBasis
          input.preparationQubits) =
      ((p18BPlus119 (executableP18Input119 source assumptions)
        (Sum.inr ()) : ℝ) : ℂ) := by
  dsimp only [FiniteScientificSource.ofAlignedCommonSource]
  rw [encodedBPlusTarget_on_extension]
  rw [executable_p18BPlus_extension_entry]

/-- The representation-capacity evidence of a theoretical source is
unchanged by its sparse finite presentation. -/
private theorem theoreticalSource_fits_finiteLayout
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source) :
    HistoryIndexFitsLayout119
      (FiniteScientificSource.ofAlignedCommonSource source).layoutSource := by
  exact ⟨fits.clock_fits, fits.label_fits⟩

/-- The finite physical history word ignores the proof-only target error and
the sparse presentation of the same theoretical initial vector. -/
private theorem theoreticalSource_finiteHistoryBasis_eq
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    finiteScientificCanonicalHistoryBasis119
        (FiniteScientificSource.ofAlignedCommonSource source).layoutSource
        (theoreticalSource_fits_finiteLayout source fits) index =
      finiteScientificCanonicalHistoryBasis119 source fits index := by
  rfl

private theorem theoreticalSource_canonicalInitialHistoryRow_eq
    (source : AlignedCommonSource119)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    canonicalInitialHistoryRow
        (FiniteScientificSource.ofAlignedCommonSource source).layoutSource
        configuration =
      canonicalInitialHistoryRow source configuration := by
  rfl

private theorem theoreticalInitialPlanBasis_injective
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    Function.Injective (fun row =>
      VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
        (dataPlacement023 input.branchQubits) (fun _ => false)
        (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
          (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
            input.layoutSource finiteFits input.branchLayout)
          (Sum.inl row))) := by
  dsimp only
  intro left right equal
  apply finiteScientificCanonicalHistoryBasis_injective source domain fits
  have innerEqual :
      finiteScientificCanonicalHistoryBasis119
          (FiniteScientificSource.ofAlignedCommonSource source).layoutSource
          (theoreticalSource_fits_finiteLayout source fits) left =
        finiteScientificCanonicalHistoryBasis119
          (FiniteScientificSource.ofAlignedCommonSource source).layoutSource
          (theoreticalSource_fits_finiteLayout source fits) right := by
    apply (ExecutableHistoryImplementationRole.finiteBranchBasisEmbedding119
      (FiniteScientificSource.ofAlignedCommonSource source).branchLayout true).injective
    apply (VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023
        (FiniteScientificSource.ofAlignedCommonSource source).branchQubits)
      (fun _ => false)).injective
    exact equal
  rw [theoreticalSource_finiteHistoryBasis_eq,
    theoreticalSource_finiteHistoryBasis_eq] at innerEqual
  exact innerEqual

private theorem theoreticalNoninitialPlanBasis_ne_encoded
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source))
    (notInitial : ∀ configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters,
      row ≠ canonicalInitialHistoryRow source configuration)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
          input.layoutSource finiteFits input.branchLayout)
        (Sum.inl row))
    basis ≠ encodedBPlusConfigurationBasis input.rhsPlacement
      input.historyControlLayout.control (finite_rhs_sign_facts input)
      configuration := by
  dsimp only
  intro equal
  have rowEqual := theoreticalInitialPlanBasis_injective source domain fits
    (equal.trans
      (scientificInitialPlanBasis_eq_encodedBPlusBasis
        (FiniteScientificSource.ofAlignedCommonSource source)
        (theoreticalSource_fits_finiteLayout source fits)
        configuration).symm)
  exact notInitial configuration rowEqual

private theorem noninitialHistoryRow_not_zero_clock_order
    (source : AlignedCommonSource119)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source))
    (notInitial : ∀ configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters,
      row ≠ canonicalInitialHistoryRow source configuration) :
    ¬ (row.clock.val = 0 ∧ row.order.val = 0) := by
  rintro ⟨clockZero, orderZero⟩
  let configuration :=
    (ProbabilityGeneratorQProof.configurationEquivCard
      source.qParameters).symm row.state
  apply notInitial configuration
  cases row with
  | mk clock order state =>
      simp only [canonicalInitialHistoryRow,
        JenningsHistory.HistoryIndex.mk.injEq]
      exact ⟨Fin.ext clockZero, Fin.ext orderZero, by
        simp [configuration]⟩

private theorem theoretical_p18BPlus_other_history_zero
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source))
    (notInitial : ∀ configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters,
      row ≠ canonicalInitialHistoryRow source configuration) :
    p18BPlus119 (executableP18Input119 source assumptions)
        (Sum.inl (legacyHistoryIndexOfCanonical119 source row)) = 0 := by
  rw [executable_p18BPlus_history_entry]
  have notZero := noninitialHistoryRow_not_zero_clock_order
    source row notInitial
  simp [legacyHistoryIndexOfCanonical119, notZero]

/-- On each initial history row, the common preparer instantiated with the
approved theoretical input has exactly the independent P18 RHS amplitude.
No numerical phase-provider output is certified by this statement. -/
theorem theoretical_rhsPreparation_initial_history_entry
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    let plan :=
      ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
        input.layoutSource finiteFits input.branchLayout
    let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        plan (Sum.inl (canonicalInitialHistoryRow input.layoutSource configuration)))
    (VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        input.rhsPreparation.circuit)
      (VerifiedCircuitCore.basisKet
        (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits)))
      basis =
      ((p18BPlus119 (executableP18Input119 source assumptions)
        (Sum.inl (initialHistoryRow source configuration)) : ℝ) : ℂ) := by
  dsimp only
  rw [scientificInitialPlanBasis_eq_encodedBPlusBasis]
  rw [theoretical_rhsPreparation_eq_encodedBPlus source assumptions]
  exact encodedBPlusTarget_eq_p18BPlus_at_configuration
    source assumptions configuration

/-- The same theoretical preparation has the independent extension amplitude
on the extension label of the finite H-history plan. -/
theorem theoretical_rhsPreparation_extension_entry
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    let plan :=
      ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
        input.layoutSource finiteFits input.branchLayout
    let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        plan (Sum.inr ()))
    (VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        input.rhsPreparation.circuit)
      (VerifiedCircuitCore.basisKet
        (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits)))
      basis =
      ((p18BPlus119 (executableP18Input119 source assumptions)
        (Sum.inr ()) : ℝ) : ℂ) := by
  dsimp only
  rw [scientificExtensionPlanBasis_zero]
  rw [theoretical_rhsPreparation_eq_encodedBPlus source assumptions]
  exact encodedBPlusTarget_eq_p18BPlus_at_extension source assumptions

/-- A theoretical history row outside the approved initial rows has zero
output amplitude under the common preparation circuit. This is not a
correctness statement about any numerical phase-provider output. -/
theorem theoretical_rhsPreparation_other_history_entry_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source))
    (notInitial : ∀ configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters,
      row ≠ canonicalInitialHistoryRow source configuration) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
          input.layoutSource finiteFits input.branchLayout)
        (Sum.inl row))
    (VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        input.rhsPreparation.circuit)
      (VerifiedCircuitCore.basisKet
        (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits)))
      basis = 0 := by
  dsimp only
  rw [theoretical_rhsPreparation_eq_encodedBPlus source assumptions]
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let finiteFits := theoreticalSource_fits_finiteLayout source fits
  let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
    (dataPlacement023 input.branchQubits) (fun _ => false)
    (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
      (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
        input.layoutSource finiteFits input.branchLayout)
      (Sum.inl row))
  change encodedBPlusTarget source.initial input.rhsPlacement
    input.historyControlLayout.control (finite_rhs_sign_facts input) basis = 0
  have notZero : basis ≠
      (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits) :=
    scientificHistoryPlanBasis_ne_zero input finiteFits row
  exact encodedBPlusTarget_zero_outside_catalog source.initial
    input.rhsPlacement input.historyControlLayout.control
    (finite_rhs_sign_facts input) basis notZero
    (fun configuration => theoreticalNoninitialPlanBasis_ne_encoded
      source domain fits row notInitial configuration)

/-- Every logical history row of the theoretical common preparer agrees with
the independent P18 vector after the proved finite/legacy reindexing. -/
theorem theoretical_rhsPreparation_all_history_entries
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (row : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    let plan :=
      ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
        input.layoutSource finiteFits input.branchLayout
    let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        plan (Sum.inl row))
    (VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        input.rhsPreparation.circuit)
      (VerifiedCircuitCore.basisKet
        (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits)))
      basis =
      ((p18BPlus119 (executableP18Input119 source assumptions)
        (Sum.inl (legacyHistoryIndexOfCanonical119 source row)) : ℝ) : ℂ) := by
  dsimp only
  by_cases isInitial : ∃ configuration :
      ProbabilityGeneratorQProof.QConfiguration source.qParameters,
      row = canonicalInitialHistoryRow source configuration
  · obtain ⟨configuration, rfl⟩ := isInitial
    simpa only [theoreticalSource_canonicalInitialHistoryRow_eq,
      canonicalInitialHistoryRow_legacy] using
      theoretical_rhsPreparation_initial_history_entry
        source assumptions fits configuration
  · have notInitial : ∀ configuration :
        ProbabilityGeneratorQProof.QConfiguration source.qParameters,
        row ≠ canonicalInitialHistoryRow source configuration := by
      intro configuration equal
      exact isInitial ⟨configuration, equal⟩
    rw [theoretical_rhsPreparation_other_history_entry_zero
      source domain assumptions fits row notInitial,
      theoretical_p18BPlus_other_history_zero
        source assumptions row notInitial]
    rfl

/-- Every extended logical label of the theoretical common preparation
agrees with the independent P18 vector. Numerical-provider outputs remain
outside the scope of this theorem. -/
theorem theoretical_rhsPreparation_all_extended_entries
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    let plan :=
      ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
        input.layoutSource finiteFits input.branchLayout
    let basis := VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        plan index)
    (VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        input.rhsPreparation.circuit)
      (VerifiedCircuitCore.basisKet
        (fun _ => false : VerifiedCircuitCore.QubitBasis input.preparationQubits)))
      basis =
      ((p18BPlus119 (executableP18Input119 source assumptions)
        (match index with
         | Sum.inl row => Sum.inl (legacyHistoryIndexOfCanonical119 source row)
         | Sum.inr _ => Sum.inr ()) : ℝ) : ℂ) := by
  cases index with
  | inl row =>
      exact theoretical_rhsPreparation_all_history_entries
        source domain assumptions fits row
  | inr extension =>
      exact theoretical_rhsPreparation_extension_entry
        source assumptions fits

/-- Theory-only physical embedding of the finite H-history plan. The
computable numerical emitter uses the same basis body but no proof-bearing
embedding or numerical accuracy claim. -/
private noncomputable def theoreticalExtendedPlanEmbedding
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) ↪
        VerifiedCircuitCore.QubitBasis
          (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits where
  toFun := fun index =>
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    VerifiedCircuitCore.finiteFixedOutsideBasisEmbedding
      (dataPlacement023 input.branchQubits) (fun _ => false)
      (ExecutableHistoryImplementationRole.finiteExtendedIndexBasisOfPlan119
        (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
          input.layoutSource finiteFits input.branchLayout)
        index)
  inj' := by
    intro left right equal
    dsimp only at equal
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let finiteFits := theoreticalSource_fits_finiteLayout source fits
    cases left with
    | inl leftRow =>
      cases right with
      | inl rightRow =>
        exact congrArg Sum.inl
          (theoreticalInitialPlanBasis_injective source domain fits equal)
      | inr extension =>
        cases extension
        exact False.elim
          ((scientificHistoryPlanBasis_ne_zero input finiteFits leftRow)
            (equal.trans (scientificExtensionPlanBasis_zero input finiteFits)))
    | inr _ =>
      cases right with
      | inl rightRow =>
        exact False.elim
          ((scientificHistoryPlanBasis_ne_zero input finiteFits rightRow)
            (equal.symm.trans
              (scientificExtensionPlanBasis_zero input finiteFits)))
      | inr _ => rfl

private theorem theoreticalExtendedPlanEmbedding_extension_eq_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    theoreticalExtendedPlanEmbedding source domain fits (Sum.inr ()) =
      (fun _ => false : VerifiedCircuitCore.QubitBasis
        (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits) := by
  exact scientificExtensionPlanBasis_zero
    (FiniteScientificSource.ofAlignedCommonSource source)
    (theoreticalSource_fits_finiteLayout source fits)

private theorem theoreticalExtendedPlanEmbedding_initial_eq_encoded
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) :
    theoreticalExtendedPlanEmbedding source domain fits
        (Sum.inl (canonicalInitialHistoryRow source configuration)) =
      encodedBPlusConfigurationBasis
        (FiniteScientificSource.ofAlignedCommonSource source).rhsPlacement
        (FiniteScientificSource.ofAlignedCommonSource source).historyControlLayout.control
        (finite_rhs_sign_facts
          (FiniteScientificSource.ofAlignedCommonSource source))
        configuration := by
  exact scientificInitialPlanBasis_eq_encodedBPlusBasis
    (FiniteScientificSource.ofAlignedCommonSource source)
    (theoreticalSource_fits_finiteLayout source fits)
    configuration

/-- A physical basis outside the theoretical extended-history embedding
cannot carry any amplitude of the independent bPlus target. -/
private theorem encodedBPlusTarget_off_theoretical_image
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (basis : VerifiedCircuitCore.QubitBasis
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits)
    (notImage : ∀ index,
      theoreticalExtendedPlanEmbedding source domain fits index ≠ basis) :
    encodedBPlusTarget source.initial
      (FiniteScientificSource.ofAlignedCommonSource source).rhsPlacement
      (FiniteScientificSource.ofAlignedCommonSource source).historyControlLayout.control
      (finite_rhs_sign_facts
        (FiniteScientificSource.ofAlignedCommonSource source)) basis = 0 := by
  apply encodedBPlusTarget_zero_outside_catalog
  · intro equal
    apply notImage (Sum.inr ())
    exact (theoreticalExtendedPlanEmbedding_extension_eq_zero
      source domain fits).trans equal.symm
  · intro configuration equal
    apply notImage (Sum.inl
      (canonicalInitialHistoryRow source configuration))
    exact (theoreticalExtendedPlanEmbedding_initial_eq_encoded
      source domain fits configuration).trans equal.symm

/-- For the approved theoretical source, the common finite preparer is the
independent P18 vector on the entire physical preparation register. This
does not assert any correctness or accuracy of a numerical-provider output. -/
theorem theoretical_rhsPreparation_eq_paddedP18
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    VerifiedCircuitCore.applyOperator
        (VerifiedCircuitCore.Circuit.denote
          (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
          input.rhsPreparation.circuit)
        (VerifiedCircuitCore.basisKet
          (fun _ => false : VerifiedCircuitCore.QubitBasis
            input.preparationQubits)) =
      ExecutableHistoryCore.paddedRealState119
        (GramOperator.ExtendedIndex
          (ExecutableD119 source) (ExecutableC119 source)
          (ExecutableLabels119 source))
        input.preparationQubits
        (theoreticalExtendedPlanEmbedding source domain fits)
        (fun index => p18BPlus119
          (executableP18Input119 source assumptions)
          (match index with
           | Sum.inl row => Sum.inl
               (legacyHistoryIndexOfCanonical119 source row)
           | Sum.inr _ => Sum.inr ())) := by
  classical
  dsimp only
  funext basis
  by_cases image : ∃ index,
      theoreticalExtendedPlanEmbedding source domain fits index = basis
  · obtain ⟨index, rfl⟩ := image
    rw [ExecutableHistoryCore.paddedRealState119_on_image]
    exact theoretical_rhsPreparation_all_extended_entries
      source domain assumptions fits index
  · have notImage : ∀ index,
        theoreticalExtendedPlanEmbedding source domain fits index ≠ basis := by
      intro index equal
      exact image ⟨index, equal⟩
    rw [ExecutableHistoryCore.paddedRealState119_off_image
      _ _ _ _ basis notImage]
    rw [theoretical_rhsPreparation_eq_encodedBPlus source assumptions]
    exact encodedBPlusTarget_off_theoretical_image
      source domain fits basis notImage

private theorem legacyHistoryIndexOfCanonical_surjective
    (source : AlignedCommonSource119) :
    Function.Surjective (legacyHistoryIndexOfCanonical119 source) := by
  intro row
  refine ⟨{ row with state :=
    (ProbabilityGeneratorQProof.canonicalToLegacyIndex
      source.qParameters).symm row.state }, ?_⟩
  cases row
  simp [legacyHistoryIndexOfCanonical119]

/-- The finite emitter's history carrier and the accepted theoretical
history carrier differ only in their source-level width expression. -/
private theorem theoreticalSource_historyQubits_eq_raw
    (source : AlignedCommonSource119) :
    (FiniteScientificSource.ofAlignedCommonSource source).historyQubits =
      (ExecutableRaw119 source).history.qubits := by
  change finiteScientificHistoryQubits119 source =
    (ExecutableRaw119 source).history.qubits
  exact finiteScientificHistoryQubits119_eq source

/-- Choose the finite emitter's branch width and control wires for the
theoretical P18 child. The sole cast changes the equivalent history-width
expressions; it does not choose a new physical placement. -/
noncomputable def theoreticalCanonicalP18CircuitSource
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    ExecutableP18CircuitSource119 source domain fits assumptions :=
  let input := FiniteScientificSource.ofAlignedCommonSource source
  { targetQubits := input.branchQubits
    layout := Eq.mp
      (congrArg (fun n => ControlLayout n
        input.branchQubits) (theoreticalSource_historyQubits_eq_raw source))
      input.branchLayout }

private theorem finiteBranchBasis_cast
    {n m target : Nat} (width : n = m)
    (layout : ControlLayout n target) (value : Bool)
    (basis : VerifiedCircuitCore.QubitBasis n) :
    finiteBranchBasisEmbedding119 layout value basis =
      finiteBranchBasisEmbedding119
        (Eq.mp (congrArg (fun count => ControlLayout count target) width)
          layout) value
        (fun wire => basis (Fin.cast width.symm wire)) := by
  cases width
  rfl

/-- The finite plan branch and the established theoretical H-history basis
use the same physical wires after a width cast and the explicit
canonical-to-legacy permutation. This does not compare circuits. -/
private theorem theoreticalFiniteBranchBasis_transport
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let width := theoreticalSource_historyQubits_eq_raw source
    let castLayout := Eq.mp
      (congrArg (fun count => ControlLayout count input.branchQubits) width)
      input.branchLayout
    finiteExtendedIndexBasisOfPlan119
        (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
          input.layoutSource (theoreticalSource_fits_finiteLayout source fits)
          input.branchLayout) index =
      match index with
      | Sum.inl row =>
          finiteBranchBasisEmbedding119 castLayout true
            (executableP18HistoryEmbedding119 source domain fits
              (legacyHistoryIndexOfCanonical119 source row))
      | Sum.inr _ =>
          finiteBranchBasisEmbedding119 castLayout false
            (zeroBasis119 (ExecutableRaw119 source).history.qubits) := by
  classical
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let width := theoreticalSource_historyQubits_eq_raw source
  let castLayout := Eq.mp
    (congrArg (fun count => ControlLayout count input.branchQubits) width)
    input.branchLayout
  cases index with
  | inl row =>
      dsimp only [finiteExtendedIndexBasisOfPlan119,
        ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119]
      have basisEq :
          (fun wire => finiteScientificCanonicalHistoryBasis119 source fits row
            (Fin.cast width.symm wire)) =
            executableP18HistoryEmbedding119 source domain fits
              (legacyHistoryIndexOfCanonical119 source row) := by
        funext wire
        exact finiteHistoryBasis_to_executableEmbedding
          source domain fits row wire
      calc
        finiteBranchBasisEmbedding119 input.branchLayout true
            (finiteScientificCanonicalHistoryBasis119 input.layoutSource
              (theoreticalSource_fits_finiteLayout source fits) row) =
          finiteBranchBasisEmbedding119 input.branchLayout true
            (finiteScientificCanonicalHistoryBasis119 source fits row) :=
            congrArg _ (theoreticalSource_finiteHistoryBasis_eq source fits row)
        _ =
          finiteBranchBasisEmbedding119 castLayout true
            (fun wire => finiteScientificCanonicalHistoryBasis119 source fits row
              (Fin.cast width.symm wire)) :=
            finiteBranchBasis_cast width input.branchLayout true _
        _ = _ := congrArg (finiteBranchBasisEmbedding119 castLayout true) basisEq
  | inr extension =>
      cases extension
      dsimp only [finiteExtendedIndexBasisOfPlan119,
        ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119]
      calc
        finiteBranchBasisEmbedding119 input.branchLayout false
            (fun _ => false) =
          finiteBranchBasisEmbedding119 castLayout false
            (fun wire => (fun _ => false) (Fin.cast width.symm wire)) :=
            finiteBranchBasis_cast width input.branchLayout false _
        _ = _ := rfl

set_option maxHeartbeats 600000
/-- Reinterpret the transport in the established internal H-history child.
Only physical basis placements are identified; no preparation-unitary
equality is asserted. -/
private theorem theoreticalFiniteBranchBasis_eq_child
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (index : GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    finiteExtendedIndexBasisOfPlan119
        (ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
          input.layoutSource (theoreticalSource_fits_finiteLayout source fits)
          input.branchLayout) index =
      extendedIndexEmbeddingF
        (executableInternalHHistory119 source domain fits assumptions
          (theoreticalCanonicalP18CircuitSource source domain fits assumptions))
        (match index with
         | Sum.inl row => Sum.inl
             (legacyHistoryIndexOfCanonical119 source row)
         | Sum.inr _ => Sum.inr ()) := by
  classical
  dsimp only
  rw [theoreticalFiniteBranchBasis_transport source domain fits index]
  cases index with
  | inl row =>
      rw [finiteBranchBasisEmbedding119_eq]
      rfl

  | inr extension =>
      cases extension
      dsimp only
      rw [finiteBranchBasisEmbedding119_eq]
      rfl

set_option maxHeartbeats 200000

/-- The outer preparation-wire placement agrees pointwise with the
established aligned P18 data embedding after history renumbering. -/
private theorem theoreticalExtendedPlanEmbedding_eq_alignedData
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (index : GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    theoreticalExtendedPlanEmbedding source domain fits index =
      ExecutableHistoryAlignedPhysicalP18.alignedDataEmbedding119
        (executableInternalHHistory119 source domain fits assumptions
          (theoreticalCanonicalP18CircuitSource source domain fits assumptions))
        (match index with
         | Sum.inl row => Sum.inl
             (legacyHistoryIndexOfCanonical119 source row)
         | Sum.inr _ => Sum.inr ()) := by
  classical
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let plan := ScientificExtractionPhysicalSpecification.finiteScientificHistorySourcePlan119
    input.layoutSource (theoreticalSource_fits_finiteLayout source fits)
    input.branchLayout
  let child := executableInternalHHistory119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  let mapped : GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) :=
    match index with
    | Sum.inl row => Sum.inl (legacyHistoryIndexOfCanonical119 source row)
    | Sum.inr _ => Sum.inr ()
  have hlast :
      (fixedOutsideBasisEmbedding
        (dataPlacement023 input.branchQubits) (fun _ => false))
        (extendedIndexEmbeddingF child mapped) =
      ExecutableHistoryAlignedPhysicalP18.alignedDataEmbedding119
        child mapped := by rfl
  have hfirst :
      theoreticalExtendedPlanEmbedding source domain fits index =
        (fixedOutsideBasisEmbedding
          (dataPlacement023 input.branchQubits) (fun _ => false))
          (extendedIndexEmbeddingF child mapped) := by
    calc
      theoreticalExtendedPlanEmbedding source domain fits index =
        (finiteFixedOutsideBasisEmbedding
          (dataPlacement023 input.branchQubits) (fun _ => false))
          (finiteExtendedIndexBasisOfPlan119 plan index) := by rfl
      _ = (fixedOutsideBasisEmbedding
          (dataPlacement023 input.branchQubits) (fun _ => false))
          (finiteExtendedIndexBasisOfPlan119 plan index) := by
        rw [finiteFixedOutsideBasisEmbedding_eq]
      _ = (fixedOutsideBasisEmbedding
          (dataPlacement023 input.branchQubits) (fun _ => false))
          (extendedIndexEmbeddingF child mapped) := by
        exact congrArg _
          (theoreticalFiniteBranchBasis_eq_child
            source domain fits assumptions index)
  exact hfirst.trans hlast

/-- The physical real amplitude prepared by the common theoretical RHS
preparer. Its definition refers to the independent P18 vector rather than to
the syntax of any earlier preparation circuit. -/
private noncomputable def theoreticalP18PhysicalAmplitude
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    VerifiedCircuitCore.QubitBasis
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits → ℝ :=
  fun basis =>
    (ExecutableHistoryCore.paddedRealState119
      (GramOperator.ExtendedIndex
        (ExecutableD119 source) (ExecutableC119 source)
        (ExecutableLabels119 source))
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits
      (theoreticalExtendedPlanEmbedding source domain fits)
      (fun index => p18BPlus119
        (executableP18Input119 source assumptions)
        (match index with
         | Sum.inl row => Sum.inl
             (legacyHistoryIndexOfCanonical119 source row)
         | Sum.inr _ => Sum.inr ())) basis).re

private noncomputable def canonicalExtendedToLegacy119
    (source : AlignedCommonSource119) :
    GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) →
    GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)
  | Sum.inl row => Sum.inl (legacyHistoryIndexOfCanonical119 source row)
  | Sum.inr _ => Sum.inr ()

private theorem canonicalExtendedToLegacy_surjective119
    (source : AlignedCommonSource119) :
    Function.Surjective (canonicalExtendedToLegacy119 source) := by
  intro index
  cases index with
  | inl row =>
      obtain ⟨canonical, equal⟩ :=
        legacyHistoryIndexOfCanonical_surjective source row
      exact ⟨Sum.inl canonical, congrArg Sum.inl equal⟩
  | inr extension =>
      cases extension
      exact ⟨Sum.inr (), rfl⟩

/-- The common preparer and the accepted aligned P18 child prescribe the
same real physical state. This is a state equality, not an equality of their
preparation unitaries. -/
private theorem theoreticalP18PhysicalAmplitude_eq_aligned119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    theoreticalP18PhysicalAmplitude source domain fits assumptions =
      ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude119
        (executableInternalHHistory119 source domain fits assumptions
          (theoreticalCanonicalP18CircuitSource source domain fits assumptions)) := by
  classical
  let child := executableInternalHHistory119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  funext basis
  by_cases image : ∃ index,
      theoreticalExtendedPlanEmbedding source domain fits index = basis
  · obtain ⟨index, equal⟩ := image
    have hleft :
        theoreticalP18PhysicalAmplitude source domain fits assumptions basis =
          p18BPlus119 (executableP18Input119 source assumptions)
            (canonicalExtendedToLegacy119 source index) := by
      rw [← equal]
      simp [theoreticalP18PhysicalAmplitude,
        ExecutableHistoryCore.paddedRealState119_on_image,
        canonicalExtendedToLegacy119]
    have hright :
        ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude119
          child basis =
          p18BPlus119 (executableP18Input119 source assumptions)
            (canonicalExtendedToLegacy119 source index) := by
      rw [← equal]
      rw [theoreticalExtendedPlanEmbedding_eq_alignedData]
      exact ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude_on_embedding119
        child (canonicalExtendedToLegacy119 source index)
    exact hleft.trans hright.symm
  · have notNew : ∀ index,
        theoreticalExtendedPlanEmbedding source domain fits index ≠ basis := by
      intro index equal
      exact image ⟨index, equal⟩
    have notOld : ∀ index,
        ExecutableHistoryAlignedPhysicalP18.alignedDataEmbedding119 child index ≠
          basis := by
      intro index equal
      obtain ⟨canonical, mapped⟩ :=
        canonicalExtendedToLegacy_surjective119 source index
      apply notNew canonical
      have placed :
          ExecutableHistoryAlignedPhysicalP18.alignedDataEmbedding119
              child (canonicalExtendedToLegacy119 source canonical) = basis := by
        rw [mapped]
        exact equal
      exact (theoreticalExtendedPlanEmbedding_eq_alignedData
        source domain fits assumptions canonical).trans placed
    have hleft :
        theoreticalP18PhysicalAmplitude source domain fits assumptions basis = 0 := by
      simp [theoreticalP18PhysicalAmplitude,
        ExecutableHistoryCore.paddedRealState119_off_image,
        notNew]
    have hright :
        ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude119
          child basis = 0 := by
      rw [ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude_eq_zeroPadded119]
      simp [ExecutableHistoryCore.zeroPaddedAmplitude119, notOld]
    exact hleft.trans hright.symm

private theorem theoreticalP18Padded_realCast
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (basis : VerifiedCircuitCore.QubitBasis
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits) :
    ExecutableHistoryCore.paddedRealState119
      (GramOperator.ExtendedIndex
        (ExecutableD119 source) (ExecutableC119 source)
        (ExecutableLabels119 source))
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits
      (theoreticalExtendedPlanEmbedding source domain fits)
      (fun index => p18BPlus119
        (executableP18Input119 source assumptions)
        (match index with
         | Sum.inl row => Sum.inl
             (legacyHistoryIndexOfCanonical119 source row)
         | Sum.inr _ => Sum.inr ())) basis =
      (theoreticalP18PhysicalAmplitude source domain fits assumptions basis : ℂ) := by
  classical
  by_cases image : ∃ index,
      theoreticalExtendedPlanEmbedding source domain fits index = basis
  · obtain ⟨index, rfl⟩ := image
    rw [ExecutableHistoryCore.paddedRealState119_on_image]
    simp [theoreticalP18PhysicalAmplitude,
      ExecutableHistoryCore.paddedRealState119_on_image]
  · have notImage : ∀ index,
        theoreticalExtendedPlanEmbedding source domain fits index ≠ basis := by
      intro index equal
      exact image ⟨index, equal⟩
    rw [ExecutableHistoryCore.paddedRealState119_off_image
      _ _ _ _ basis notImage]
    simp [theoreticalP18PhysicalAmplitude,
      ExecutableHistoryCore.paddedRealState119_off_image, notImage]

/-- The common preparer meets the exact physical zero-column condition used
by the aligned P18 theorem. -/
theorem theoretical_rhsPreparation_aligned_zero_column
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    ∀ basis : VerifiedCircuitCore.QubitBasis
        (ExecutableHistoryAlignedPhysicalP18.AlignedDataQubits119 child),
      VerifiedCircuitCore.Circuit.denote
          (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
          input.rhsPreparation.circuit basis
          (ExecutableHistoryCore.zeroBasis119
            (ExecutableHistoryAlignedPhysicalP18.AlignedDataQubits119 child)) =
        (ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude119
          child basis : ℂ) := by
  classical
  dsimp only
  intro basis
  have prepared := congrFun
    (theoretical_rhsPreparation_eq_paddedP18
      source domain assumptions fits) basis
  have realCast := theoreticalP18Padded_realCast
    source domain fits assumptions basis
  have physical := theoreticalP18PhysicalAmplitude_eq_aligned119
    source domain fits assumptions
  change (VerifiedCircuitCore.Circuit.denote
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
      (FiniteScientificSource.ofAlignedCommonSource source).rhsPreparation.circuit)
        basis (fun _ => false) =
      (ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude119
        (executableInternalHHistory119 source domain fits assumptions
          (theoreticalCanonicalP18CircuitSource source domain fits assumptions))
        basis : ℂ)
  calc
    _ = (theoreticalP18PhysicalAmplitude
          source domain fits assumptions basis : ℂ) := by
      simpa only [ExecutableHistoryQbPlusCleanBlock.applyOperator_basisKet119]
        using prepared.trans realCast
    _ = _ := congrArg (fun state => (state basis : ℂ)) physical

/-- The P18 logical block built with the common preparer is exactly the
independently specified Gram operator. The proof uses its prepared state,
never an equality with the earlier preparation circuit. -/
theorem theoretical_rhsPreparation_alignedP18_logical_block
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (output inputIndex : GramOperator.ExtendedIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (ExecutableHistoryAlignedPhysicalP18.alignedP18CircuitWithPreparation119
          child input.rhsPreparation)
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child output)
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child inputIndex) =
      (GramOperator.gNuOperator
        (executableP18Input119 source assumptions).base.system
        (executableP18Input119 source assumptions).base.alpha
        (executableP18Input119 source assumptions).base.nu
        output inputIndex : ℂ) := by
  classical
  dsimp only
  exact ExecutableHistoryAlignedPhysicalP18Block.alignedP18WithPreparation_logical_block119
    (executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions))
    (FiniteScientificSource.ofAlignedCommonSource source).rhsPreparation
    (theoretical_rhsPreparation_aligned_zero_column
      source domain fits assumptions)
    assumptions.one_le_nu output inputIndex

/-- The finite history emitter has the accepted H-history word after the
source-width cast. This lemma compares only the history child, not the old
and new state preparation circuits. -/
private theorem theoreticalFiniteHistory_flatten_eq_child
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    ((theoreticalSource_historyQubits_eq_raw source) ▸ input.historyCircuit).flatten =
      child.circuit.circuit.flatten := by
  classical
  dsimp only
  change ((finiteScientificHistoryQubits119_eq source) ▸
    ExecutableHistoryFiniteScientificH3.finiteScientificCorrectedP05Circuit119
      source).flatten = _
  rw [ExecutableHistoryFiniteScientificP05Bridge.finiteScientificCorrectedP05_eq_certified
    source domain]
  rw [ExecutableHistoryFiniteCorrectedP05.certifiedPlan_compile_eq]
  exact ExecutableHistoryExecutableHistory.finiteCorrectedP05CertifiedProjection119_flatten_eq
    source domain

/-- A one-control rotation word depends on the value of its closed angle,
not on which finite angle syntax represents that value. -/
private theorem singletonNegativeRy_denote_congr
    {qubits : Nat} (control scratch target : Fin qubits)
    (left right : VerifiedCircuitCore.AngleExpr)
    (same : left.uniformValue = right.uniformValue) :
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (VerifiedCircuitCore.Circuit.boolMultiControlledRy
          [(control, false)] [scratch] target left) =
      VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (VerifiedCircuitCore.Circuit.boolMultiControlledRy
          [(control, false)] [scratch] target right) := by
  have half :
      (VerifiedCircuitCore.uniformHalfAngle left).eval (fun _ => 0) =
        (VerifiedCircuitCore.uniformHalfAngle right).eval (fun _ => 0) := by
    simpa [VerifiedCircuitCore.uniformHalfAngle,
      VerifiedCircuitCore.AngleExpr.uniformValue,
      VerifiedCircuitCore.AngleExpr.eval] using
        congrArg (fun value : ℝ => value / 2) same
  rw [VerifiedCircuitCore.uniformBoolMultiControlledRyCircuit_denote_eq_analyticOperator,
    VerifiedCircuitCore.uniformBoolMultiControlledRyCircuit_denote_eq_analyticOperator]
  by_cases different : control ≠ target
  · simp only [VerifiedCircuitCore.uniformBoolMultiControlledRyAnalyticOperator,
      List.map_cons, List.map_nil,
      VerifiedCircuitCore.uniformPositiveMultiControlledRyAnalyticOperator,
      dif_pos different]
    simp [VerifiedCircuitCore.uniformControlledRyDecompositionAnalyticOperator,
      VerifiedCircuitCore.AngleExpr.eval, half]
  · simp [VerifiedCircuitCore.uniformBoolMultiControlledRyAnalyticOperator,
      VerifiedCircuitCore.uniformPositiveMultiControlledRyAnalyticOperator,
      different]

/-- Control compilation transports the already-proved finite history gate
sequence through the source-width cast. No state-preparer equality is used. -/
theorem theoreticalFiniteBranchControl_flatten
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    (controlCircuit input.branchLayout input.branchHistory).circuit.flatten =
      (controlCircuit child.layout child.circuit).circuit.flatten := by
  classical
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let width := theoreticalSource_historyQubits_eq_raw source
  let child := executableInternalHHistory119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  have history :
      (Eq.mp (congrArg NormalizedCircuit width) input.branchHistory).circuit.flatten =
        child.circuit.circuit.flatten := by
    rw [normalizedCircuit_source_cast_circuit]
    exact theoreticalFiniteHistory_flatten_eq_child source domain fits assumptions
  change (controlCircuit input.branchLayout input.branchHistory).circuit.flatten =
    (controlCircuit child.layout child.circuit).circuit.flatten
  rw [← controlCircuit_source_cast width input.branchLayout input.branchHistory]
  exact controlCircuit_flatten_congr child.layout _ child.circuit history

/-- The finite branch and the analytic branch have the same operator when
their extension-angle values agree. No syntax equality is required. -/
theorem theoreticalFiniteHnuBranchWithAngle_denote
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (extensionAngle : VerifiedCircuitCore.AngleExpr)
    (extensionAngle_value : extensionAngle.uniformValue = hnuAngleF assumptions.nu) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (input.hnuBranchWithAngle extensionAngle).circuit =
      VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuExtensionNormalizedF child assumptions.nu).circuit := by
  classical
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let child := executableInternalHHistory119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  have controlled : Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (controlCircuit input.branchLayout input.branchHistory).circuit =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlCircuit child.layout child.circuit).circuit :=
    Circuit.denote_eq_of_flatten _ _ _
      (theoreticalFiniteBranchControl_flatten source domain fits assumptions)
  have angle : extensionAngle.uniformValue =
      (VerifiedCircuitCore.AngleExpr.const (hnuAngleF assumptions.nu)).uniformValue := by
    exact extensionAngle_value
  have rotation := singletonNegativeRy_denote_congr
    input.branchLayout.control (input.branchLayout.work 0)
    (input.branchLayout.work 1) extensionAngle
    (.const (hnuAngleF assumptions.nu)) angle
  have control_eq : child.layout.control = input.branchLayout.control := by
    exact controlLayout_source_cast_control
      (theoreticalSource_historyQubits_eq_raw source) input.branchLayout
  have work_eq : ∀ slot, child.layout.work slot = input.branchLayout.work slot := by
    intro slot
    exact controlLayout_source_cast_work
      (theoreticalSource_historyQubits_eq_raw source) input.branchLayout slot
  change VerifiedCircuitCore.Circuit.denote _
      (VerifiedCircuitCore.Circuit.sequence [
        (controlCircuit input.branchLayout input.branchHistory).circuit,
        VerifiedCircuitCore.Circuit.boolMultiControlledRy
          [(input.branchLayout.control, false)] [input.branchLayout.work 0]
          (input.branchLayout.work 1) extensionAngle]) =
    VerifiedCircuitCore.Circuit.denote _
      (VerifiedCircuitCore.Circuit.sequence [hnuControlCircuitF child,
        hnuRotationCircuitF child assumptions.nu])
  simp only [VerifiedCircuitCore.Circuit.denote_sequence_eq_operatorSequence,
    List.map_cons, List.map_nil, VerifiedCircuitCore.operatorSequence,
    Matrix.one_mul, hnuControlCircuitF, hnuRotationCircuitF,
    control_eq, work_eq, controlled, rotation]
  rfl

theorem doubleWireLift_denote_congr {n m k : Nat}
    (first : Fin n ↪ Fin m) (second : Fin m ↪ Fin k)
    (left right : Circuit (PrimitiveGate n))
    (same : Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) left =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) right)
    (tail : Circuit (PrimitiveGate k)) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.sequence [
          (left.mapGates (PrimitiveGate.mapWires first)).mapGates
            (PrimitiveGate.mapWires second), tail]) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.sequence [
          (right.mapGates (PrimitiveGate.mapWires first)).mapGates
            (PrimitiveGate.mapWires second), tail]) := by
  simp only [Circuit.denote_sequence_eq_operatorSequence, List.map_cons,
    List.map_nil, operatorSequence, Matrix.one_mul,
    denote_mapPrimitiveWires_eq_wireLiftOperator, same]

/-- The entire finite P18 signal, not just its RHS preparation, transports to
the established analytic P18 operator. This is the connection needed before
the outer QSVT builder can be shared by both provider modes. -/
theorem theoreticalFiniteP18WithAngle_denote
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (extensionAngle : VerifiedCircuitCore.AngleExpr)
    (extensionAngle_value : extensionAngle.uniformValue = hnuAngleF assumptions.nu) :
    let input := FiniteScientificSource.ofAlignedCommonSource source
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (input.p18CircuitWithAngle extensionAngle) =
      VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
        (ExecutableHistoryAlignedPhysicalP18.alignedP18CircuitWithPreparation119
          child input.rhsPreparation) := by
  classical
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let child := executableInternalHHistory119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  exact doubleWireLift_denote_congr
    (dataPlacement023 input.branchQubits)
    (ExecutableHistoryQbPlusCleanBlock.dataPlacement119 input.preparationQubits)
    (input.hnuBranchWithAngle extensionAngle).circuit
    (hnuExtensionNormalizedF child assumptions.nu).circuit
    (theoreticalFiniteHnuBranchWithAngle_denote source domain fits assumptions
      extensionAngle extensionAngle_value)
    (ExecutableHistoryQbPlusCleanBlock.qBPlusBlockCircuit119 input.rhsPreparation)

/-- Real-to-angle adaptation stays outside the finite construction. The
scientific nu=1 path uses exactly the finite zero-angle syntax. -/
noncomputable def theoreticalExtensionAngle (nu : ℝ) : VerifiedCircuitCore.AngleExpr :=
  if nu = 1 then rationalAngle 0 else .const (hnuAngleF nu)

theorem theoreticalExtensionAngle_value (nu : ℝ) :
    (theoreticalExtensionAngle nu).uniformValue = hnuAngleF nu := by
  classical
  by_cases one : nu = 1
  · subst nu
    norm_num [theoreticalExtensionAngle, rationalAngle, AngleExpr.uniformValue,
      AngleExpr.eval, hnuAngleF]
  · simp [theoreticalExtensionAngle, one, AngleExpr.uniformValue]

/-- The theory-only signal program uses the common finite RHS preparer in the
same P18 assembly that accepts the certified H-history child. The numerical
phase provider is not assigned a mathematical accuracy certificate here. -/
noncomputable def canonicalCommonP18SignalProgram
    (source : AlignedCommonSource119)
    (_domain : ExecutableHistoryDomain119 source)
    (_fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    NativeSignalQSVTGeneric.Program
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits :=
  { signalCircuit :=
      (FiniteScientificSource.ofAlignedCommonSource source).p18CircuitWithAngle
        (theoreticalExtensionAngle assumptions.nu) }

/-- The signal block supplied to the generic QSVT compiler is the independent
Gram operator, not a syntactic surrogate defined from the emitted circuit. -/
theorem canonicalCommonP18Signal_cleanBlock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    NativeSingularPairTwoFrame.cleanBlock
        (VerifiedCircuitCore.Circuit.denote
          (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
          (canonicalCommonP18SignalProgram
            source domain fits assumptions).signalCircuit)
        (NativeSingularPairTwoFrame.basisKetEmbeddingMatrix
          (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child)) =
      fun output inputIndex =>
        (GramOperator.gNuOperator
          (executableP18Input119 source assumptions).base.system
          (executableP18Input119 source assumptions).base.alpha
          (executableP18Input119 source assumptions).base.nu
          output inputIndex : ℂ) := by
  classical
  dsimp only
  change NativeSingularPairTwoFrame.cleanBlock
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        ((FiniteScientificSource.ofAlignedCommonSource source).p18CircuitWithAngle
          (theoreticalExtensionAngle assumptions.nu))) _ = _
  rw [theoreticalFiniteP18WithAngle_denote source domain fits assumptions
    (theoreticalExtensionAngle assumptions.nu) (theoreticalExtensionAngle_value _)]
  ext output inputIndex
  rw [NativeSingularPairTwoFrame.cleanBlock_basisKetEmbeddingMatrix_apply]
  exact theoretical_rhsPreparation_alignedP18_logical_block
    source domain fits assumptions output inputIndex

set_option maxHeartbeats 1200000

/-- Proof-only interface for a signal already constructed by a finite
builder. This is not an argument of the public circuit constructor. Each
application must construct this evidence internally from its preparation
theorem; no external numerical-provider accuracy is asserted. -/
class CommonP18Implementation
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) where
  signalCircuit : Circuit (PrimitiveGate
    (FiniteScientificSource.ofAlignedCommonSource source).p18Qubits)
  cleanBlock :
    NativeSingularPairTwoFrame.cleanBlock
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) signalCircuit)
      (NativeSingularPairTwoFrame.basisKetEmbeddingMatrix
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119
          (executableInternalHHistory119 source domain fits assumptions
            (theoreticalCanonicalP18CircuitSource source domain fits assumptions)))) =
      NativeConcreteP18QSPWitness.executableGNuOperator119 source assumptions

set_option maxHeartbeats 200000

/-- Compatibility instance for the previously proved dense presentation. -/
noncomputable instance (priority := 10) canonicalCommonP18Implementation
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    CommonP18Implementation source domain fits assumptions where
  signalCircuit := (canonicalCommonP18SignalProgram source domain fits assumptions).signalCircuit
  cleanBlock := canonicalCommonP18Signal_cleanBlock source domain fits assumptions

noncomputable def theoreticalCommonP18SignalProgram
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [implementation : CommonP18Implementation source domain fits assumptions] :
    NativeSignalQSVTGeneric.Program
      (FiniteScientificSource.ofAlignedCommonSource source).preparationQubits :=
  { signalCircuit := implementation.signalCircuit }

theorem theoreticalCommonP18Signal_cleanBlock
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [implementation : CommonP18Implementation source domain fits assumptions] :
    NativeSingularPairTwoFrame.cleanBlock
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit)
      (NativeSingularPairTwoFrame.basisKetEmbeddingMatrix
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119
          (executableInternalHHistory119 source domain fits assumptions
            (theoreticalCanonicalP18CircuitSource source domain fits assumptions)))) =
      NativeConcreteP18QSPWitness.executableGNuOperator119 source assumptions :=
  implementation.cleanBlock

/-- The new signal supplies the generic QSVT two-frame construction with
exactly the old independent singular-pair equations. The proof uses only the
new circuit's unitary denotation and its proved clean block. -/
noncomputable def theoreticalCommonP18StrictPairData
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [CommonP18Implementation source domain fits assumptions]
    (pair : NativeConcreteP18QSPWitness.ExecutableP18StrictSingularPair119
      source assumptions) :
    let child := executableInternalHHistory119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    NativeSingularPairTwoFrame.StrictSingularPairData
      (VerifiedCircuitCore.QubitBasis
        (ExecutableHistoryAlignedPhysicalP18.AlignedTotalQubits119 child))
      (GramOperator.ExtendedIndex
        (ExecutableD119 source) (ExecutableC119 source)
        (ExecutableLabels119 source)) := by
  classical
  let child := executableInternalHHistory119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  let U : Operator (QubitBasis
      (ExecutableHistoryAlignedPhysicalP18.AlignedTotalQubits119 child)) :=
    VerifiedCircuitCore.Circuit.denote
    (VerifiedCircuitCore.primitiveGateOperatorWithSymbols (fun _ => 0))
    (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit
  let E := NativeSingularPairTwoFrame.basisKetEmbeddingMatrix
    (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child)
  have block : NativeSingularPairTwoFrame.cleanBlock U E =
      NativeConcreteP18QSPWitness.executableGNuOperator119
        source assumptions := by
    exact theoreticalCommonP18Signal_cleanBlock source domain fits assumptions
  refine
    { U := U
      E := E
      sigma := pair.sigma
      g := pair.g
      v := pair.v
      u := pair.u
      U_star_right := ?_
      U_star_left := ?_
      E_isometry := ?_
      singular_forward := ?_
      singular_adjoint := ?_
      completion := pair.completion
      g_ne_zero := pair.g_ne_zero }
  · exact (Matrix.mem_unitaryGroup_iff).mp
      (VerifiedCircuitCore.primitiveCircuit_denote_mem_unitaryGroup
        (fun _ : String => 0)
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit)
  · exact (Matrix.mem_unitaryGroup_iff').mp
      (VerifiedCircuitCore.primitiveCircuit_denote_mem_unitaryGroup
        (fun _ : String => 0)
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit)
  · exact NativeSingularPairTwoFrame.basisKetEmbeddingMatrix_isometry
      (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child)
  · rw [block]
    exact pair.singular_forward
  · rw [block]
    exact pair.singular_adjoint

/-- The new signal closes the strict forward two-frame QSVT equation. -/
theorem theoreticalCommonP18_twoFrame_forward
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [CommonP18Implementation source domain fits assumptions]
    (pair : NativeConcreteP18QSPWitness.ExecutableP18StrictSingularPair119
      source assumptions) :
    let data := theoreticalCommonP18StrictPairData
      source domain fits assumptions pair
    data.U * NativeSingularPairTwoFrame.sourceFrame data =
      NativeSingularPairTwoFrame.targetFrame data *
        NativeSingularPairTwoFrame.singularTransferMatrix data.sigma data.g := by
  exact NativeSingularPairTwoFrame.strictFrame_forward
    (theoreticalCommonP18StrictPairData source domain fits assumptions pair)

/-- The inverse signal obeys the matching strict adjoint equation. -/
theorem theoreticalCommonP18_twoFrame_adjoint
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [CommonP18Implementation source domain fits assumptions]
    (pair : NativeConcreteP18QSPWitness.ExecutableP18StrictSingularPair119
      source assumptions) :
    let data := theoreticalCommonP18StrictPairData
      source domain fits assumptions pair
    Matrix.conjTranspose data.U * NativeSingularPairTwoFrame.targetFrame data =
      NativeSingularPairTwoFrame.sourceFrame data *
        Matrix.conjTranspose
          (NativeSingularPairTwoFrame.singularTransferMatrix data.sigma data.g) := by
  exact NativeSingularPairTwoFrame.strictFrame_adjoint
    (theoreticalCommonP18StrictPairData source domain fits assumptions pair)

private theorem signal_zero_basis_eq_aligned_block (n : Nat)
    (data : VerifiedCircuitCore.QubitBasis n) :
    NativeSignalPhase.basis n 0 data =
      ExecutableHistoryQbPlusCleanBlock.blockBasis119 data := by
  funext wire
  by_cases h : wire = ExecutableHistoryQbPlusCleanBlock.signalWire119 n
  · subst wire
    simp [NativeSignalPhase.basis,
      ExecutableHistoryQbPlusCleanBlock.blockBasis119_signal]
  · exact NativeSignalPhase.basis_outside_signal n 0 data wire h

/-- The source projector used by the widened QSP compiler is precisely the
clean embedding of the new aligned P18 signal.  This identifies the physical
image, not the old and new preparation unitaries. -/
theorem theoreticalCommonSourceEmbedding_eq_aligned
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source) :
    let circuitSource := theoreticalCanonicalP18CircuitSource
      source domain fits assumptions
    NativeSignalQSVTActual.executableSignalSourceEmbedding119
        source domain fits assumptions circuitSource =
      ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119
        (executableInternalHHistory119 source domain fits assumptions circuitSource) := by
  classical
  intro circuitSource
  ext index wire
  change NativeSignalPhase.basis _ 0 _ wire =
    ExecutableHistoryQbPlusCleanBlock.blockBasis119 _ wire
  exact congrFun (signal_zero_basis_eq_aligned_block _ _) wire

noncomputable def theoreticalHistoryRenumber (source : AlignedCommonSource119) :
    JenningsHistory.HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) ≃
    JenningsHistory.HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) where
  toFun := legacyHistoryIndexOfCanonical119 source
  invFun := fun row => { row with
    state := (ProbabilityGeneratorQProof.canonicalToLegacyIndex source.qParameters).symm row.state }
  left_inv := by
    intro row
    cases row
    simp [legacyHistoryIndexOfCanonical119]
  right_inv := by
    intro row
    cases row
    simp [legacyHistoryIndexOfCanonical119]

noncomputable def theoreticalExtendedRenumber (source : AlignedCommonSource119) :
    GramOperator.ExtendedIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) ≃
    GramOperator.ExtendedIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) :=
  Equiv.sumCongr (theoreticalHistoryRenumber source) (Equiv.refl Unit)

theorem theoreticalFiniteSourceBasis_eq
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (index : GramOperator.ExtendedIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    (FiniteScientificSource.ofAlignedCommonSource source).sourceBasis
        (theoreticalSource_fits_finiteLayout source fits) index =
      NativeSignalQSVTActual.executableSignalSourceEmbedding119
        source domain fits assumptions
        (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
        (theoreticalExtendedRenumber source index) := by
  change NativeSignalQSVTActual.finiteSignalBasis119 _ 0
      (theoreticalExtendedPlanEmbedding source domain fits index) = _
  rw [NativeSignalQSVTActual.finiteSignalBasis119_eq,
    theoreticalExtendedPlanEmbedding_eq_alignedData source domain fits assumptions index]
  cases index <;> rfl

noncomputable def theoreticalFinitePhaseCircuit
    (source : AlignedCommonSource119) (fits : HistoryIndexFitsLayout119 source)
    (angle : VerifiedCircuitCore.AngleExpr) :
    Circuit (PrimitiveGate (FiniteScientificSource.ofAlignedCommonSource source).phaseQubits) :=
  (FiniteScientificSource.ofAlignedCommonSource source).imagePhaseCircuit
    (theoreticalSource_fits_finiteLayout source fits) angle

theorem theoreticalFinitePhase_apply_clean_state
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (angle : VerifiedCircuitCore.AngleExpr)
    (state : State (QubitBasis (FiniteScientificSource.ofAlignedCommonSource source).p18Qubits)) :
    let embedding := NativeSignalQSVTActual.executableSignalSourceEmbedding119
      source domain fits assumptions (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (theoreticalFinitePhaseCircuit source fits angle))
      (fixedOutsideStateEmbedding
        (NativeEmbeddingImagePhase.standardImagePhasePlacement
          (FiniteScientificSource.ofAlignedCommonSource source).p18Qubits)
        (fun _ => false) state) =
      fixedOutsideStateEmbedding
        (NativeEmbeddingImagePhase.standardImagePhasePlacement
          (FiniteScientificSource.ofAlignedCommonSource source).p18Qubits)
        (fun _ => false)
        (applyOperator (NativeEmbeddingImagePhase.sourceImagePhaseOperator
          embedding angle.uniformValue) state) := by
  classical
  let input := FiniteScientificSource.ofAlignedCommonSource source
  let embedding : GramOperator.ExtendedIndex (ExecutableD119 source)
      (ExecutableC119 source) (ExecutableLabels119 source) ↪ QubitBasis input.p18Qubits :=
    NativeSignalQSVTActual.executableSignalSourceEmbedding119
      source domain fits assumptions (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
  unfold theoreticalFinitePhaseCircuit
  exact input.imagePhaseCircuit_apply_clean_state
    (theoreticalSource_fits_finiteLayout source fits)
    (theoreticalExtendedRenumber source) embedding
    (theoreticalFiniteSourceBasis_eq source domain fits assumptions)
    angle state

/-- The full finite outer QSVT compiler can be instantiated with the new
P18 signal. Projector phases and the external-control layout retain the
certified physical image; only the preparation inside the signal changes. -/
noncomputable def theoreticalCommonOuterPlan
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [CommonP18Implementation source domain fits assumptions] :
    let circuitSource := theoreticalCanonicalP18CircuitSource
      source domain fits assumptions
    M13bFiniteOuterCompiler.Plan
      (NativeConcreteP18QSPWitness.widenedP18Qubits119
        source domain fits assumptions circuitSource) := by
  classical
  exact
    { signalCircuit :=
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit.mapGates
          (PrimitiveGate.mapWires (NativeEmbeddingImagePhase.standardImagePhasePlacement
            (FiniteScientificSource.ofAlignedCommonSource source).p18Qubits))
      sourcePhase := theoreticalFinitePhaseCircuit source fits
      targetPhase := theoreticalFinitePhaseCircuit source fits
      layout := externalControlLayout
        (FiniteScientificSource.ofAlignedCommonSource source).phaseQubits }

attribute [irreducible] theoreticalCommonOuterPlan

/-- The proof-side outer compiler takes the new finite P18 signal as its
actual forward query. This is a circuit-construction identity, not an
assertion that two preparation unitaries are equal. -/
theorem theoreticalCommonOuterPlan_signalCircuit
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [CommonP18Implementation source domain fits assumptions] :
    (theoreticalCommonOuterPlan source domain fits assumptions).signalCircuit =
      (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit.mapGates
        (VerifiedCircuitCore.PrimitiveGate.mapWires
          (VerifiedCircuitCore.NativeEmbeddingImagePhase.standardImagePhasePlacement
            (NativeSignalQSVTActual.ExecutableSignalP18Qubits119
              source domain fits assumptions
              (theoreticalCanonicalP18CircuitSource source domain fits assumptions)))) := by
  unfold theoreticalCommonOuterPlan
  rfl

/-- Both phase roles are generated by the same finite image enumerator used
by numerical construction. Their clean-state meaning was proved above. -/
theorem theoreticalCommonOuterPlan_phaseCircuits
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [CommonP18Implementation source domain fits assumptions]
    (angle : VerifiedCircuitCore.AngleExpr) :
    (theoreticalCommonOuterPlan source domain fits assumptions).sourcePhase angle =
        theoreticalFinitePhaseCircuit source fits angle ∧
      (theoreticalCommonOuterPlan source domain fits assumptions).targetPhase angle =
        theoreticalFinitePhaseCircuit source fits angle := by
  constructor <;> unfold theoreticalCommonOuterPlan <;> rfl

theorem theoreticalFinitePhase_denote_eval
    (source : AlignedCommonSource119) (fits : HistoryIndexFitsLayout119 source)
    (angle : VerifiedCircuitCore.AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (theoreticalFinitePhaseCircuit source fits angle) =
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (theoreticalFinitePhaseCircuit source fits (.const angle.uniformValue)) := by
  exact NativeExactBasisPhase.booleanProgramPhaseCircuitExpr_denote _ _ _ _ _

end QLean.Circuits.FiniteScientificPreparationBridge

