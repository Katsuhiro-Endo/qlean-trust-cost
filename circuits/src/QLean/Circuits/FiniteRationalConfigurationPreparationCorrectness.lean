import QLean.Circuits.FiniteRationalConfigurationPreparation
import QLean.Circuits.Foundation.UniformPreparationCorrectness
import QLean.Circuits.Foundation.ShuklaVedulaUniformCorrectness
import QLean.Circuits.Foundation.OperatorL2Error

/-!
# Clean-scratch action of one finite sparse-preparation rotation

These lemmas are generic circuit-semantics tools for the theoretical
state-preparation proof. They do not certify any numerical provider output.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness

open VerifiedCircuitCore
open QLean.Circuits.FiniteRationalConfigurationPreparation

noncomputable section

/-- Algebraic bridge used only when the shared preparer is instantiated with
the approved theoretical initial vector.  It is not a certification of an
externally supplied numerical phase program. -/
theorem signed_sqrt_square_over_positive
    (amplitude root : ℝ) (rootPos : 0 < root) :
    (if amplitude < 0 then (-1 : ℝ) else 1) *
        Real.sqrt (amplitude ^ 2 / root) =
      amplitude / Real.sqrt root := by
  have rootNonneg : 0 ≤ root := le_of_lt rootPos
  rw [Real.sqrt_div (sq_nonneg amplitude), Real.sqrt_sq_eq_abs]
  by_cases negative : amplitude < 0
  · have absValue : |amplitude| = -amplitude :=
      abs_of_neg negative
    simp [negative, absValue]
    ring
  · have amplitudeNonneg : 0 ≤ amplitude := le_of_not_gt negative
    have absValue : |amplitude| = amplitude :=
      abs_of_nonneg amplitudeNonneg
    simp [negative, absValue]

/-- If specified orthogonal outputs already carry all probability mass of
a normalized theoretical state, every other physical basis amplitude is
zero.  This is a general finite-state fact, not a numerical-output claim. -/
theorem normalized_state_zero_outside_saturated
    {basis : Type} [Fintype basis] [DecidableEq basis]
    (state : State basis) (normalized : IsNormalizedState state)
    (selected : Finset basis)
    (saturated : (∑ index ∈ selected, Complex.normSq (state index)) = 1)
    (index : basis) (outside : index ∉ selected) : state index = 0 := by
  have total : (∑ current : basis, Complex.normSq (state current)) = 1 := by
    simpa [IsNormalizedState, basisProbability] using normalized
  have bounded :
      (∑ current ∈ insert index selected,
        Complex.normSq (state current)) ≤
      ∑ current : basis, Complex.normSq (state current) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro current _ _
    exact Complex.normSq_nonneg _
  rw [Finset.sum_insert outside, saturated, total] at bounded
  have normZero : Complex.normSq (state index) = 0 := by
    have nonneg := Complex.normSq_nonneg (state index)
    linarith
  exact Complex.normSq_eq_zero.mp normZero

/-- The theoretical rational initial vector becomes a normalized real
configuration vector after division by the root branch mass. -/
theorem SparseInitial.ofAmplitude_normalized_real_mass
    {p : ProbabilityGeneratorQProof.QParameters}
    (amplitude : ProbabilityGeneratorQProof.QConfiguration p → ℚ)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0) :
    (∑ configuration : ProbabilityGeneratorQProof.QConfiguration p,
      ((amplitude configuration : ℝ) /
        Real.sqrt
          (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ)) ^ 2) =
      1 := by
  let root : ℝ :=
    (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ)
  have rootPosReal : 0 < root := by
    dsimp [root]
    exact_mod_cast rootPos
  have rootEq :
      root = ∑ configuration : ProbabilityGeneratorQProof.QConfiguration p,
        (amplitude configuration : ℝ) ^ 2 := by
    dsimp [root]
    exact_mod_cast SparseInitial.branchMass_root_ofAmplitude amplitude
  have term (configuration : ProbabilityGeneratorQProof.QConfiguration p) :
      ((amplitude configuration : ℝ) / Real.sqrt root) ^ 2 =
        (amplitude configuration : ℝ) ^ 2 / root := by
    rw [div_pow, Real.sq_sqrt (le_of_lt rootPosReal)]
  change (∑ configuration : ProbabilityGeneratorQProof.QConfiguration p,
    ((amplitude configuration : ℝ) / Real.sqrt root) ^ 2) = 1
  simp_rw [term]
  rw [← Finset.sum_div, ← rootEq]
  exact div_self (ne_of_gt rootPosReal)

theorem half_branch_normSq (value : ℝ) :
    Complex.normSq ((((1 / Real.sqrt 2 : ℝ) * value) : ℝ) : ℂ) =
      value ^ 2 / 2 := by
  rw [Complex.normSq_ofReal]
  calc
    _ = (1 / Real.sqrt 2 : ℝ) ^ 2 * value ^ 2 := by ring
    _ = value ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

def SupportedOnScratchZero {qubits : Nat}
    (scratches : List (Fin qubits))
    (state : State (QubitBasis qubits)) : Prop :=
  ∀ basis, (∃ wire ∈ scratches, basis wire = true) → state basis = 0

def SupportedOnBranchFalse {qubits : Nat}
    (branch : Fin qubits) (state : State (QubitBasis qubits)) : Prop :=
  ∀ basis, basis branch = true → state basis = 0

theorem boolMultiControlledRy_applyOperator_eq_ideal
    {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy controls scratches target angle)) state =
      applyOperator
        (boolControlledRyOperator controls target angle.uniformValue) state := by
  funext output
  unfold applyOperator Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro input _
  by_cases scratchZero : ∀ wire ∈ scratches, input wire = false
  · change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.boolMultiControlledRy controls scratches target angle)
        output input * state input =
      boolControlledRyAmplitude controls target angle.uniformValue output input *
        state input
    rw [boolMultiControlledRy_apply_sparse controls scratches target angle
      output input enoughScratch layoutNodup scratchZero]
  · have dirty : ∃ wire ∈ scratches, input wire = true := by
      push Not at scratchZero
      rcases scratchZero with ⟨wire, member, notFalse⟩
      refine ⟨wire, member, ?_⟩
      cases bit : input wire with
      | false => exact (notFalse bit).elim
      | true => rfl
    rw [support input dirty]
    simp

theorem boolMultiControlledRy_applyOperator
    {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy controls scratches target angle))
        state output =
      if boolControlsSatisfied controls output then
        ∑ inputBit : Bool,
          localRy angle.uniformValue (output target) inputBit *
            state (replaceQubitWire output target inputBit)
      else state output := by
  rw [boolMultiControlledRy_applyOperator_eq_ideal controls scratches target
    angle enoughScratch layoutNodup state support]
  have targetOutside : target ∉ controls.map Prod.fst := by
    intro member
    have separated := (List.nodup_append.mp layoutNodup).2.2
    exact separated target (List.mem_append_left scratches member)
      target (List.mem_cons_self) rfl
  exact applyOperator_boolControlledRyOperator controls target targetOutside
    angle.uniformValue state output

theorem boolMultiControlledRy_preserves_scratchZero
    {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state) :
    SupportedOnScratchZero scratches
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy controls scratches target angle)) state) := by
  intro output dirty
  rw [boolMultiControlledRy_applyOperator controls scratches target angle
    enoughScratch layoutNodup state support output]
  have targetOutsideScratch : target ∉ scratches := by
    intro member
    have separated := (List.nodup_append.mp layoutNodup).2.2
    exact separated target (List.mem_append_right (controls.map Prod.fst) member)
      target (List.mem_cons_self) rfl
  have dirtyAfterReplace : ∀ value : Bool,
      ∃ wire ∈ scratches, replaceQubitWire output target value wire = true := by
    intro value
    rcases dirty with ⟨wire, member, wireTrue⟩
    refine ⟨wire, member, ?_⟩
    rw [replaceQubitWire_outside]
    · exact wireTrue
    · intro equal
      subst wire
      exact targetOutsideScratch member
  by_cases enabled : boolControlsSatisfied controls output
  · simp only [enabled, if_true]
    apply Finset.sum_eq_zero
    intro value _
    rw [support _ (dirtyAfterReplace value)]
    simp
  · simp [enabled, support output dirty]

/-- A clean-work controlled rotation cannot populate a wire other than its
target. This preserves the untouched higher data bits in the theoretical
prefix-by-prefix preparation. -/
theorem boolMultiControlledRy_preserves_false_wire
    {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (wire : Fin qubits) (wireOutsideTarget : wire ≠ target)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (supportWire : ∀ basis, basis wire = true → state basis = 0) :
    ∀ output, output wire = true →
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy controls scratches target angle))
        state output = 0 := by
  intro output outputTrue
  rw [boolMultiControlledRy_applyOperator controls scratches target angle
    enoughScratch layoutNodup state supportScratch output]
  by_cases enabled : boolControlsSatisfied controls output = true
  · simp only [enabled, if_true]
    apply Finset.sum_eq_zero
    intro inputBit _
    have inputTrue :
        replaceQubitWire output target inputBit wire = true := by
      rw [replaceQubitWire_outside output target wire inputBit
        wireOutsideTarget]
      exact outputTrue
    rw [supportWire _ inputTrue]
    simp
  · have disabled : boolControlsSatisfied controls output = false := by
      cases result : boolControlsSatisfied controls output <;> simp_all
    simp [disabled, supportWire output outputTrue]

/-- A controlled rotation cannot create amplitude in a target-bit fiber
whose two input amplitudes both vanish. This local fact will handle zero-mass
prefixes in the theoretical state-preparation induction. -/
theorem boolMultiControlledRy_preserves_zero_fiber
    {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits)
    (fiberZero : ∀ value : Bool,
      state (replaceQubitWire output target value) = 0) :
    ∀ value : Bool,
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy controls scratches target angle))
        state (replaceQubitWire output target value) = 0 := by
  intro value
  rw [boolMultiControlledRy_applyOperator controls scratches target angle
    enoughScratch layoutNodup state supportScratch
    (replaceQubitWire output target value)]
  by_cases enabled : boolControlsSatisfied controls
      (replaceQubitWire output target value) = true
  · simp only [enabled, ite_true]
    apply Finset.sum_eq_zero
    intro inputBit _
    have replaceSame :
        replaceQubitWire (replaceQubitWire output target value) target
            inputBit = replaceQubitWire output target inputBit := by
      funext wire
      by_cases equal : wire = target <;> simp [replaceQubitWire, equal]
    rw [replaceSame, fiberZero inputBit]
    simp
  · have disabled : boolControlsSatisfied controls
        (replaceQubitWire output target value) = false := by
      cases result : boolControlsSatisfied controls
          (replaceQubitWire output target value) <;> simp_all
    simp [disabled, fiberZero value]

/-- A branch-controlled rotation is the identity on a state supported on the
opposite branch.  This isolates the extension branch of the theoretical
`bPlus` preparation; it is not a numerical-output accuracy statement. -/
theorem boolMultiControlledRy_identity_on_false_branch
    {qubits : Nat} (branch : Fin qubits)
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : ((branch, true) :: controls).length ≤ scratches.length + 1)
    (layoutNodup :
      (((branch, true) :: controls).map Prod.fst ++ scratches ++ [target]).Nodup)
    (targetOutsideBranch : branch ≠ target)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (supportBranch : SupportedOnBranchFalse branch state) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy ((branch, true) :: controls)
            scratches target angle)) state = state := by
  funext output
  rw [boolMultiControlledRy_applyOperator ((branch, true) :: controls)
    scratches target angle enoughScratch layoutNodup state supportScratch
    output]
  by_cases branchTrue : output branch = true
  · have inputZero : ∀ inputBit : Bool,
        state (replaceQubitWire output target inputBit) = 0 := by
      intro inputBit
      apply supportBranch
      rw [replaceQubitWire_outside output target branch inputBit
        targetOutsideBranch]
      exact branchTrue
    by_cases enabled : boolControlsSatisfied ((branch, true) :: controls)
        output = true
    · simp only [enabled, if_true]
      rw [supportBranch output branchTrue]
      apply Finset.sum_eq_zero
      intro inputBit _
      rw [inputZero inputBit]
      simp
    · have disabled : boolControlsSatisfied ((branch, true) :: controls)
          output = false := by
        cases value : boolControlsSatisfied ((branch, true) :: controls) output <;>
          simp_all
      simp [disabled]
  · have branchFalse : output branch = false := by
      cases value : output branch <;> simp_all
    have disabled : boolControlsSatisfied ((branch, true) :: controls)
        output = false := by
      simp [boolControlsSatisfied, branchFalse]
    simp [disabled]

theorem boolMultiControlledRy_false_branch_output
    {qubits : Nat} (branch : Fin qubits)
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr)
    (enoughScratch : ((branch, true) :: controls).length ≤ scratches.length + 1)
    (layoutNodup :
      (((branch, true) :: controls).map Prod.fst ++ scratches ++ [target]).Nodup)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy ((branch, true) :: controls)
            scratches target angle)) state output = state output := by
  rw [boolMultiControlledRy_applyOperator ((branch, true) :: controls)
    scratches target angle enoughScratch layoutNodup state supportScratch
    output]
  have disabled : boolControlsSatisfied ((branch, true) :: controls)
      output = false := by
    simp [boolControlsSatisfied, branchFalse]
  simp [disabled]

/-- An internal well-laid-out rotation instruction. The scientific circuit
still supplies the actual prefix data and angle; this record carries only
the generic wire obligations needed by the clean-scratch proof. -/
structure CleanRotationInstruction (qubits : Nat)
    (scratches : List (Fin qubits)) where
  controls : List (Fin qubits × Bool)
  target : Fin qubits
  angle : AngleExpr
  enoughScratch : controls.length ≤ scratches.length + 1
  layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup

def CleanRotationInstruction.compile {qubits : Nat}
    {scratches : List (Fin qubits)}
    (instruction : CleanRotationInstruction qubits scratches) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.boolMultiControlledRy instruction.controls scratches
    instruction.target instruction.angle

theorem CleanRotationInstruction.targetOutsideControls
    {qubits : Nat} {scratches : List (Fin qubits)}
    (instruction : CleanRotationInstruction qubits scratches) :
    instruction.target ∉ instruction.controls.map Prod.fst := by
  intro member
  have separated := (List.nodup_append.mp instruction.layoutNodup).2.2
  exact separated instruction.target
    (List.mem_append_left scratches member)
    instruction.target (List.mem_cons_self) rfl

theorem compiledCleanRotations_preserve_scratchZero
    {qubits : Nat} (scratches : List (Fin qubits))
    (instructions : List (CleanRotationInstruction qubits scratches))
    (state : State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state) :
    SupportedOnScratchZero scratches
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map CleanRotationInstruction.compile)))
        state) := by
  induction instructions generalizing state with
  | nil =>
      simpa [Circuit.sequence, Circuit.denote, applyOperator] using support
  | cons instruction rest inductionHypothesis =>
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      exact inductionHypothesis _
        (boolMultiControlledRy_preserves_scratchZero instruction.controls
          scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state support)

theorem compiledCleanRotations_preserve_false_wire
    {qubits : Nat} (scratches : List (Fin qubits))
    (instructions : List (CleanRotationInstruction qubits scratches))
    (wire : Fin qubits)
    (wireOutsideTargets : ∀ instruction ∈ instructions,
      wire ≠ instruction.target)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (supportWire : ∀ basis, basis wire = true → state basis = 0) :
    ∀ output, output wire = true →
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence
            (instructions.map CleanRotationInstruction.compile)))
        state output = 0 := by
  induction instructions generalizing state with
  | nil =>
      simpa [Circuit.sequence, Circuit.denote, applyOperator] using supportWire
  | cons instruction rest inductionHypothesis =>
      have restOutside : ∀ next ∈ rest, wire ≠ next.target := by
        intro next member
        exact wireOutsideTargets next (by simp [member])
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have nextScratch : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state) :=
        boolMultiControlledRy_preserves_scratchZero instruction.controls
          scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state
          supportScratch
      have nextWire : ∀ basis, basis wire = true →
          applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state basis = 0 := by
        simpa only [CleanRotationInstruction.compile] using
          boolMultiControlledRy_preserves_false_wire instruction.controls
            scratches instruction.target instruction.angle
            instruction.enoughScratch instruction.layoutNodup wire
            (wireOutsideTargets instruction (by simp)) state supportScratch
            supportWire
      exact inductionHypothesis restOutside _ nextScratch nextWire

/-- A whole layer of rotations about one target preserves a zero-amplitude
target fiber. This is the circuit-side zero-parent-mass case. -/
theorem compiledCleanRotations_preserves_zero_fiber
    {qubits : Nat} (scratches : List (Fin qubits))
    (instructions : List (CleanRotationInstruction qubits scratches))
    (target : Fin qubits)
    (sameTarget : ∀ instruction ∈ instructions,
      instruction.target = target)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits)
    (fiberZero : ∀ value : Bool,
      state (replaceQubitWire output target value) = 0) :
    ∀ value : Bool,
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence
            (instructions.map CleanRotationInstruction.compile)))
        state (replaceQubitWire output target value) = 0 := by
  induction instructions generalizing state with
  | nil =>
      simpa [Circuit.sequence, Circuit.denote, applyOperator] using fiberZero
  | cons instruction rest inductionHypothesis =>
      have restSame : ∀ next ∈ rest, next.target = target := by
        intro next member
        exact sameTarget next (by simp [member])
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have nextScratch : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state) :=
        boolMultiControlledRy_preserves_scratchZero instruction.controls
          scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state
          supportScratch
      have nextFiber : ∀ value : Bool,
          applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state
            (replaceQubitWire output target value) = 0 := by
        intro value
        rw [← sameTarget instruction (by simp)]
        exact boolMultiControlledRy_preserves_zero_fiber
          instruction.controls scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state
          supportScratch output
          (by simpa only [sameTarget instruction (by simp)] using fiberZero)
          value
      exact inductionHypothesis restSame _ nextScratch nextFiber

/-- If no active control pattern matches an output basis, a magnitude layer
leaves that output amplitude unchanged. This is used for the theoretical
state-preparation proof, including the zero-amplitude branches. -/
theorem compiledCleanRotations_output_of_all_disabled
    {qubits : Nat} (scratches : List (Fin qubits))
    (instructions : List (CleanRotationInstruction qubits scratches))
    (state : State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits)
    (disabled : ∀ instruction ∈ instructions,
      boolControlsSatisfied instruction.controls output = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map CleanRotationInstruction.compile)))
        state output = state output := by
  induction instructions generalizing state with
  | nil =>
      simp [Circuit.sequence, Circuit.denote, applyOperator]
  | cons instruction rest inductionHypothesis =>
      have restDisabled : ∀ next ∈ rest,
          boolControlsSatisfied next.controls output = false := by
        intro next member
        exact disabled next (by simp [member])
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have nextSupport : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state) :=
        boolMultiControlledRy_preserves_scratchZero instruction.controls
          scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state support
      rw [inductionHypothesis _ nextSupport restDisabled]
      simp only [CleanRotationInstruction.compile]
      rw [boolMultiControlledRy_applyOperator instruction.controls scratches
        instruction.target instruction.angle instruction.enoughScratch
        instruction.layoutNodup state support output]
      simp [disabled instruction (by simp)]

/-- Disabling every rotation at a basis also disables it on the two-point
fiber obtained by changing the common target bit. -/
theorem compiledCleanRotations_fiber_of_all_disabled
    {qubits : Nat} (scratches : List (Fin qubits))
    (instructions : List (CleanRotationInstruction qubits scratches))
    (target : Fin qubits)
    (sameTarget : ∀ instruction ∈ instructions, instruction.target = target)
    (state : State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits)
    (disabled : ∀ instruction ∈ instructions,
      boolControlsSatisfied instruction.controls output = false)
    (value : Bool) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map CleanRotationInstruction.compile)))
        state (replaceQubitWire output target value) =
      state (replaceQubitWire output target value) := by
  apply compiledCleanRotations_output_of_all_disabled scratches instructions
    state support
  intro instruction member
  have targetOutside := instruction.targetOutsideControls
  have preserved := boolControlsSatisfied_replaceQubitWire
    instruction.controls instruction.target targetOutside output value
  rw [sameTarget instruction member] at preserved
  exact preserved.trans (disabled instruction member)

theorem compiledCleanRotations_split_denote
    {qubits : Nat} (scratches : List (Fin qubits))
    (before after : List (CleanRotationInstruction qubits scratches))
    (middle : CleanRotationInstruction qubits scratches) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.sequence
          ((before ++ middle :: after).map CleanRotationInstruction.compile)) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (after.map CleanRotationInstruction.compile)) *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          middle.compile *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (before.map CleanRotationInstruction.compile)) := by
  simp only [Circuit.denote_sequence_eq_operatorSequence, List.map_append,
    List.map_cons, operatorSequence_append, operatorSequence, mul_assoc]

/-- A magnitude layer with one matching prefix has exactly the local `Ry`
action of that prefix. Other prefixes cannot modify either amplitude in the
target-bit fiber. This is a circuit lemma for the theoretical preparation. -/
theorem compiledCleanRotations_single_active_output
    {qubits : Nat} (scratches : List (Fin qubits))
    (before after : List (CleanRotationInstruction qubits scratches))
    (selected : CleanRotationInstruction qubits scratches)
    (sameTargetBefore : ∀ instruction ∈ before,
      instruction.target = selected.target)
    (state : State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits)
    (beforeDisabled : ∀ instruction ∈ before,
      boolControlsSatisfied instruction.controls output = false)
    (selectedEnabled : boolControlsSatisfied selected.controls output = true)
    (afterDisabled : ∀ instruction ∈ after,
      boolControlsSatisfied instruction.controls output = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence
            ((before ++ selected :: after).map
              CleanRotationInstruction.compile))) state output =
      ∑ inputBit : Bool,
        localRy selected.angle.uniformValue (output selected.target) inputBit *
          state (replaceQubitWire output selected.target inputBit) := by
  let beforeState := applyOperator
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (Circuit.sequence (before.map CleanRotationInstruction.compile))) state
  have beforeSupport : SupportedOnScratchZero scratches beforeState :=
    compiledCleanRotations_preserve_scratchZero scratches before state support
  have selectedSupport : SupportedOnScratchZero scratches
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          selected.compile) beforeState) :=
    boolMultiControlledRy_preserves_scratchZero selected.controls scratches
      selected.target selected.angle selected.enoughScratch
      selected.layoutNodup beforeState beforeSupport
  rw [compiledCleanRotations_split_denote scratches before after selected,
    applyOperator_mul, applyOperator_mul]
  rw [compiledCleanRotations_output_of_all_disabled scratches after _
    selectedSupport output afterDisabled]
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        selected.compile) beforeState output = _
  simp only [CleanRotationInstruction.compile]
  rw [boolMultiControlledRy_applyOperator selected.controls scratches
    selected.target selected.angle selected.enoughScratch selected.layoutNodup
    beforeState beforeSupport output]
  simp only [selectedEnabled, ite_true]
  apply Finset.sum_congr rfl
  intro inputBit _
  dsimp only [beforeState]
  rw [compiledCleanRotations_fiber_of_all_disabled scratches before
    selected.target sameTargetBefore state support output beforeDisabled
    inputBit]

theorem compiledCleanRotations_identity_on_false_branch
    {qubits : Nat} (scratches : List (Fin qubits))
    (branch : Fin qubits)
    (instructions : List (CleanRotationInstruction qubits scratches))
    (branchControlled : ∀ instruction ∈ instructions,
      ∃ controls, instruction.controls = (branch, true) :: controls ∧
        branch ≠ instruction.target)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (supportBranch : SupportedOnBranchFalse branch state) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map CleanRotationInstruction.compile)))
        state = state := by
  induction instructions with
  | nil =>
      simp [Circuit.sequence, Circuit.denote, applyOperator]
  | cons instruction rest inductionHypothesis =>
      obtain ⟨controls, controlEq, targetOutside⟩ :=
        branchControlled instruction (by simp)
      have restControlled : ∀ next ∈ rest,
          ∃ controls, next.controls = (branch, true) :: controls ∧
            branch ≠ next.target := by
        intro next member
        exact branchControlled next (by simp [member])
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have firstIdentity :
          applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state = state := by
        simpa only [CleanRotationInstruction.compile, controlEq] using
          boolMultiControlledRy_identity_on_false_branch branch controls
            scratches instruction.target instruction.angle
            (controlEq ▸ instruction.enoughScratch)
            (controlEq ▸ instruction.layoutNodup) targetOutside state
            supportScratch supportBranch
      rw [firstIdentity]
      exact inductionHypothesis restControlled

theorem compiledCleanRotations_false_branch_output
    {qubits : Nat} (scratches : List (Fin qubits))
    (branch : Fin qubits)
    (instructions : List (CleanRotationInstruction qubits scratches))
    (branchControlled : ∀ instruction ∈ instructions,
      ∃ controls, instruction.controls = (branch, true) :: controls)
    (state : State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map CleanRotationInstruction.compile)))
        state output = state output := by
  induction instructions generalizing state with
  | nil =>
      simp [Circuit.sequence, Circuit.denote, applyOperator]
  | cons instruction rest inductionHypothesis =>
      obtain ⟨controls, controlEq⟩ :=
        branchControlled instruction (by simp)
      have restControlled : ∀ next ∈ rest,
          ∃ controls, next.controls = (branch, true) :: controls := by
        intro next member
        exact branchControlled next (by simp [member])
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have nextSupport : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state) := by
        exact boolMultiControlledRy_preserves_scratchZero
          instruction.controls scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state supportScratch
      rw [inductionHypothesis restControlled _ nextSupport]
      simpa only [CleanRotationInstruction.compile, controlEq] using
        boolMultiControlledRy_false_branch_output branch controls scratches
          instruction.target instruction.angle
          (controlEq ▸ instruction.enoughScratch)
          (controlEq ▸ instruction.layoutNodup) state supportScratch output
          branchFalse

open ProbabilityGeneratorQProof

/-- Circuit-only placement obligations for the prefix rotations. The
scientific input and target state are not bundled into these wire facts. -/
structure MagnitudePlacementFacts {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) : Prop where
  dataInjective : Function.Injective placement.data
  scratchNodup : placement.scratch.Nodup
  dataOutsideScratch : ∀ bit, placement.data bit ∉ placement.scratch
  scratchLength : p.systemWidth ≤ placement.scratch.length

theorem prefixControlsAt_layoutNodup
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (facts : MagnitudePlacementFacts placement)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    ((prefixControlsAt placement depth pattern).map Prod.fst ++
      placement.scratch ++ [placement.data depth]).Nodup := by
  have controlInjective : Function.Injective
      (fun bit : Fin depth.val =>
        placement.data ⟨bit.val, by omega⟩) := by
    intro left right equal
    have values := congrArg Fin.val (facts.dataInjective equal)
    exact Fin.ext values
  have controlsNodup :
      ((prefixControlsAt placement depth pattern).map Prod.fst).Nodup := by
    simp only [prefixControlsAt, List.map_map]
    exact List.Nodup.map controlInjective (List.nodup_finRange depth.val)
  have controlsScratchDisjoint :
      ((prefixControlsAt placement depth pattern).map Prod.fst).Disjoint
        placement.scratch := by
    rw [List.disjoint_left]
    intro wire controlMember scratchMember
    simp only [prefixControlsAt, List.map_map] at controlMember
    rcases List.mem_map.mp controlMember with ⟨bit, _, rfl⟩
    exact facts.dataOutsideScratch _ scratchMember
  have targetOutsideControls :
      placement.data depth ∉
        (prefixControlsAt placement depth pattern).map Prod.fst := by
    intro member
    simp only [prefixControlsAt, List.map_map] at member
    rcases List.mem_map.mp member with ⟨bit, _, equal⟩
    have values := congrArg Fin.val (facts.dataInjective equal)
    exact (Nat.ne_of_lt bit.isLt) values
  have prefixNodup :
      ((prefixControlsAt placement depth pattern).map Prod.fst ++
        placement.scratch).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨controlsNodup, facts.scratchNodup, ?_⟩
    intro left leftMember right rightMember equal
    subst right
    exact (List.disjoint_left.mp controlsScratchDisjoint)
      leftMember rightMember
  apply List.nodup_append.mpr
  refine ⟨prefixNodup, by simp, ?_⟩
  intro wire member finalTarget finalMember equal
  have finalEqual : finalTarget = placement.data depth := by
    simpa using finalMember
  subst finalTarget
  subst wire
  rcases List.mem_append.mp member with controlMember | scratchMember
  · exact targetOutsideControls controlMember
  · exact facts.dataOutsideScratch depth scratchMember

/-- The extra branch control must remain outside both the configuration data
and the clean work register.  These are wire facts for the shared preparation
builder, not a scientific claim about an externally supplied phase word. -/
structure BranchPlacementFacts {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits) : Prop
    extends MagnitudePlacementFacts placement where
  branchOutsideData : ∀ bit, branch ≠ placement.data bit
  branchOutsideScratch : branch ∉ placement.scratch

/-- Proof-local injective view of the preparation data wires. -/
private def SparseInitial.dataEmbedding
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (facts : MagnitudePlacementFacts placement) :
    Fin p.systemWidth ↪ Fin qubits where
  toFun := placement.data
  inj' := facts.dataInjective

/-- Canonical physical basis for one theoretical branch prefix. Outside the
data register only the branch bit is set; unprocessed data bits are zero. -/
def SparseInitial.prefixBasis
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count pattern : Nat) : QubitBasis qubits :=
  let dataEmbedding :=
    SparseInitial.dataEmbedding placement facts.toMagnitudePlacementFacts
  VerifiedCircuitCore.fixedOutsideBasisEmbedding dataEmbedding
    (fun outside => if outside.1 = branch then true else false)
    (fun bit => if bit.val < count then pattern.testBit bit.val else false)

private theorem SparseInitial.prefixBasis_data
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count pattern : Nat) (bit : Fin p.systemWidth) :
    SparseInitial.prefixBasis placement branch facts count pattern
        (placement.data bit) =
      if bit.val < count then pattern.testBit bit.val else false := by
  let dataEmbedding :=
    SparseInitial.dataEmbedding placement facts.toMagnitudePlacementFacts
  have readBack := congrFun
    (VerifiedCircuitCore.restrictToPlacedWires_mergePlacedAndOutsideBasis
      dataEmbedding
      (fun bit => if bit.val < count then pattern.testBit bit.val else false)
      (fun outside => if outside.1 = branch then true else false)) bit
  simpa [SparseInitial.prefixBasis, dataEmbedding,
    VerifiedCircuitCore.restrictToPlacedWires,
    VerifiedCircuitCore.fixedOutsideBasisEmbedding,
    SparseInitial.dataEmbedding] using readBack

private theorem SparseInitial.prefixBasis_branch
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count pattern : Nat) :
    SparseInitial.prefixBasis placement branch facts count pattern branch =
      true := by
  let dataEmbedding :=
    SparseInitial.dataEmbedding placement facts.toMagnitudePlacementFacts
  let outsideBranch : VerifiedCircuitCore.OutsideWire dataEmbedding :=
    ⟨branch, by
      intro bit equal
      exact facts.branchOutsideData bit equal.symm⟩
  have readBack := congrFun
    (VerifiedCircuitCore.restrictToOutsideWires_mergePlacedAndOutsideBasis
      dataEmbedding
      (fun bit => if bit.val < count then pattern.testBit bit.val else false)
      (fun outside => if outside.1 = branch then true else false))
    outsideBranch
  simpa [SparseInitial.prefixBasis, dataEmbedding, outsideBranch,
    VerifiedCircuitCore.restrictToOutsideWires,
    VerifiedCircuitCore.fixedOutsideBasisEmbedding,
    SparseInitial.dataEmbedding] using readBack

private theorem SparseInitial.prefixBasis_outside_data
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count pattern : Nat) (wire : Fin qubits)
    (outside : ∀ bit, placement.data bit ≠ wire) :
    SparseInitial.prefixBasis placement branch facts count pattern wire =
      if wire = branch then true else false := by
  let dataEmbedding :=
    SparseInitial.dataEmbedding placement facts.toMagnitudePlacementFacts
  have noSource : ¬∃ source, dataEmbedding source = wire := by
    rintro ⟨source, equal⟩
    exact outside source equal
  change VerifiedCircuitCore.mergePlacedAndOutsideBasis dataEmbedding
    (fun bit => if bit.val < count then pattern.testBit bit.val else false)
    (fun other => if other.1 = branch then true else false) wire = _
  simp [VerifiedCircuitCore.mergePlacedAndOutsideBasis, noSource]

private theorem SparseInitial.prefixBasis_scratch_false
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count pattern : Nat) (wire : Fin qubits)
    (member : wire ∈ placement.scratch) :
    SparseInitial.prefixBasis placement branch facts count pattern wire =
      false := by
  have outside : ∀ bit, placement.data bit ≠ wire := by
    intro bit equal
    exact facts.dataOutsideScratch bit (equal.symm ▸ member)
  have notBranch : wire ≠ branch := by
    intro equal
    exact facts.branchOutsideScratch (equal ▸ member)
  rw [SparseInitial.prefixBasis_outside_data placement branch facts
    count pattern wire outside]
  simp [notBranch]

private theorem SparseInitial.prefixBasis_zero_eq_branch_one
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch) :
    SparseInitial.prefixBasis placement branch facts 0 0 =
      replaceQubitWire (fun _ => false : QubitBasis qubits) branch true := by
  funext wire
  by_cases atBranch : wire = branch
  · subst wire
    rw [SparseInitial.prefixBasis_branch, replaceQubitWire_target]
  · by_cases atData : ∃ bit, placement.data bit = wire
    · obtain ⟨bit, equal⟩ := atData
      subst wire
      rw [SparseInitial.prefixBasis_data]
      have notBranch : placement.data bit ≠ branch := by
        intro equalBranch
        exact facts.branchOutsideData bit equalBranch.symm
      simp [replaceQubitWire, notBranch]
    · have outside : ∀ bit, placement.data bit ≠ wire := by
        intro bit equal
        exact atData ⟨bit, equal⟩
      rw [SparseInitial.prefixBasis_outside_data placement branch facts
        0 0 wire outside]
      simp [replaceQubitWire, atBranch]

private theorem SparseInitial.prefixBasis_step
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    SparseInitial.prefixBasis placement branch facts (depth.val + 1) pattern =
      replaceQubitWire
        (SparseInitial.prefixBasis placement branch facts depth.val pattern)
        (placement.data depth) (pattern.testBit depth.val) := by
  funext wire
  by_cases target : wire = placement.data depth
  · subst wire
    rw [SparseInitial.prefixBasis_data, replaceQubitWire_target]
    simp
  · by_cases inData : ∃ bit, placement.data bit = wire
    · obtain ⟨bit, rfl⟩ := inData
      have bitNe : bit ≠ depth := by
        intro same
        subst bit
        exact target rfl
      have bitValNe : bit.val ≠ depth.val := by
        intro same
        exact bitNe (Fin.ext same)
      rw [SparseInitial.prefixBasis_data,
        replaceQubitWire_outside _ _ _ _ target,
        SparseInitial.prefixBasis_data]
      by_cases before : bit.val < depth.val
      · have next : bit.val < depth.val + 1 := by omega
        simp [before, next]
      · have next : ¬bit.val < depth.val + 1 := by omega
        simp [before, next]
    · have outside : ∀ bit, placement.data bit ≠ wire := by
        intro bit equal
        exact inData ⟨bit, equal⟩
      rw [SparseInitial.prefixBasis_outside_data placement branch facts
        (depth.val + 1) pattern wire outside,
        replaceQubitWire_outside _ _ _ _ target,
        SparseInitial.prefixBasis_outside_data placement branch facts
          depth.val pattern wire outside]

private theorem SparseInitial.prefixBasis_eq_of_low_bits
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count left right : Nat)
    (sameLowBits : ∀ bit : Fin p.systemWidth, bit.val < count →
      left.testBit bit.val = right.testBit bit.val) :
    SparseInitial.prefixBasis placement branch facts count left =
      SparseInitial.prefixBasis placement branch facts count right := by
  funext wire
  by_cases inData : ∃ bit, placement.data bit = wire
  · obtain ⟨bit, rfl⟩ := inData
    rw [SparseInitial.prefixBasis_data,
      SparseInitial.prefixBasis_data]
    by_cases before : bit.val < count
    · simp [before, sameLowBits bit before]
    · simp [before]
  · have outside : ∀ bit, placement.data bit ≠ wire := by
      intro bit equal
      exact inData ⟨bit, equal⟩
    rw [SparseInitial.prefixBasis_outside_data placement branch facts
      count left wire outside,
      SparseInitial.prefixBasis_outside_data placement branch facts
        count right wire outside]

private theorem SparseInitial.prefixBasis_add_pow
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    SparseInitial.prefixBasis placement branch facts depth.val
        (pattern + 2 ^ depth.val) =
      SparseInitial.prefixBasis placement branch facts depth.val pattern := by
  apply SparseInitial.prefixBasis_eq_of_low_bits placement branch facts
  intro bit before
  exact testBit_add_pow_of_lt depth.val pattern bit.val patternBound before

private theorem SparseInitial.prefixBasis_left_child
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        pattern =
      replaceQubitWire
        (SparseInitial.prefixBasis placement branch facts depth.val pattern)
        (placement.data depth) false := by
  rw [SparseInitial.prefixBasis_step]
  rw [Nat.testBit_lt_two_pow patternBound]

private theorem SparseInitial.prefixBasis_right_child
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        (pattern + 2 ^ depth.val) =
      replaceQubitWire
        (SparseInitial.prefixBasis placement branch facts depth.val pattern)
        (placement.data depth) true := by
  rw [SparseInitial.prefixBasis_step,
    testBit_add_pow_at depth.val pattern patternBound,
    SparseInitial.prefixBasis_add_pow placement branch facts depth pattern
      patternBound]

private theorem replaceQubitWire_twice
    {qubits : Nat} (basis : QubitBasis qubits) (target : Fin qubits)
    (first second : Bool) :
    replaceQubitWire (replaceQubitWire basis target first) target second =
      replaceQubitWire basis target second := by
  funext wire
  by_cases same : wire = target <;> simp [replaceQubitWire, same]

private theorem SparseInitial.prefixBasis_current_target_false
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    SparseInitial.prefixBasis placement branch facts depth.val pattern
        (placement.data depth) = false := by
  rw [SparseInitial.prefixBasis_data]
  simp

private theorem SparseInitial.prefixBasis_left_child_parent
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    replaceQubitWire
        (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
          pattern)
        (placement.data depth) false =
      SparseInitial.prefixBasis placement branch facts depth.val pattern := by
  rw [SparseInitial.prefixBasis_left_child placement branch facts depth pattern
    patternBound, replaceQubitWire_twice]
  simpa [SparseInitial.prefixBasis_current_target_false placement branch facts
    depth pattern] using
    (replaceQubitWire_self
      (SparseInitial.prefixBasis placement branch facts depth.val pattern)
      (placement.data depth))

private theorem SparseInitial.prefixBasis_right_child_parent
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    replaceQubitWire
        (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
          (pattern + 2 ^ depth.val))
        (placement.data depth) false =
      SparseInitial.prefixBasis placement branch facts depth.val pattern := by
  rw [SparseInitial.prefixBasis_right_child placement branch facts depth pattern
    patternBound, replaceQubitWire_twice]
  simpa [SparseInitial.prefixBasis_current_target_false placement branch facts
    depth pattern] using
    (replaceQubitWire_self
      (SparseInitial.prefixBasis placement branch facts depth.val pattern)
      (placement.data depth))

theorem prefixControlsAtWhen_enoughScratch
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    ((branch, true) :: prefixControlsAt placement depth pattern).length ≤
      placement.scratch.length + 1 := by
  simp only [List.length_cons, prefixControlsAt, List.length_map,
    List.length_finRange]
  have depthBound := depth.isLt
  have scratchBound := facts.scratchLength
  omega

theorem prefixControlsAtWhen_layoutNodup
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    ((((branch, true) :: prefixControlsAt placement depth pattern).map
        Prod.fst) ++ placement.scratch ++ [placement.data depth]).Nodup := by
  simp only [List.map_cons]
  apply List.nodup_cons.mpr
  constructor
  · intro member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with controlMember | scratchMember
      · simp only [prefixControlsAt, List.map_map] at controlMember
        rcases List.mem_map.mp controlMember with ⟨bit, _, equal⟩
        exact facts.branchOutsideData _ equal.symm
      · exact facts.branchOutsideScratch scratchMember
    · have targetEqual : branch = placement.data depth := by
        simpa using member
      exact facts.branchOutsideData depth targetEqual
  · exact prefixControlsAt_layoutNodup placement facts.toMagnitudePlacementFacts
      depth pattern

private theorem prefixControlsAtWhen_targetOutside
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    placement.data depth ∉
      (((branch, true) :: prefixControlsAt placement depth pattern).map
        Prod.fst) := by
  have layout := prefixControlsAtWhen_layoutNodup placement branch facts
    depth pattern
  have separated := (List.nodup_append.mp layout).2.2
  intro member
  exact separated (placement.data depth)
    (List.mem_append_left placement.scratch member)
    (placement.data depth) (List.mem_cons_self) rfl

theorem prefixControlsAtWhen_satisfied_iff
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (output : QubitBasis qubits) :
    boolControlsSatisfied
        ((branch, true) :: prefixControlsAt placement depth pattern)
        output = true ↔
      output branch = true ∧
        ∀ bit : Fin depth.val,
          output (placement.data ⟨bit.val, by omega⟩) =
            pattern.testBit bit.val := by
  simp [boolControlsSatisfied, prefixControlsAt, List.all_eq_true]

private theorem SparseInitial.prefixBasis_controls
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    boolControlsSatisfied
        ((branch, true) :: prefixControlsAt placement depth pattern)
        (SparseInitial.prefixBasis placement branch facts depth.val pattern) =
      true := by
  apply (prefixControlsAtWhen_satisfied_iff placement branch depth pattern
    (SparseInitial.prefixBasis placement branch facts depth.val pattern)).2
  constructor
  · exact SparseInitial.prefixBasis_branch placement branch facts depth.val
      pattern
  · intro bit
    have data := SparseInitial.prefixBasis_data placement branch facts
      depth.val pattern ⟨bit.val, by omega⟩
    simpa [bit.isLt] using data

private theorem SparseInitial.prefixBasis_left_child_controls
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    boolControlsSatisfied
        ((branch, true) :: prefixControlsAt placement depth pattern)
        (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
          pattern) = true := by
  rw [SparseInitial.prefixBasis_left_child placement branch facts depth pattern
    patternBound,
    boolControlsSatisfied_replaceQubitWire _ _
      (prefixControlsAtWhen_targetOutside placement branch facts depth pattern)]
  exact SparseInitial.prefixBasis_controls placement branch facts depth pattern

private theorem SparseInitial.prefixBasis_right_child_controls
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val) :
    boolControlsSatisfied
        ((branch, true) :: prefixControlsAt placement depth pattern)
        (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
          (pattern + 2 ^ depth.val)) = true := by
  rw [SparseInitial.prefixBasis_right_child placement branch facts depth pattern
    patternBound,
    boolControlsSatisfied_replaceQubitWire _ _
      (prefixControlsAtWhen_targetOutside placement branch facts depth pattern)]
  exact SparseInitial.prefixBasis_controls placement branch facts depth pattern

theorem prefixControlsAtWhen_unique
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (depth : Fin p.systemWidth) (left right : Nat)
    (leftBound : left < 2 ^ depth.val)
    (rightBound : right < 2 ^ depth.val)
    (output : QubitBasis qubits)
    (leftMatch : boolControlsSatisfied
      ((branch, true) :: prefixControlsAt placement depth left) output = true)
    (rightMatch : boolControlsSatisfied
      ((branch, true) :: prefixControlsAt placement depth right) output = true) :
    left = right := by
  obtain ⟨_, leftBits⟩ :=
    (prefixControlsAtWhen_satisfied_iff placement branch depth left output).mp
      leftMatch
  obtain ⟨_, rightBits⟩ :=
    (prefixControlsAtWhen_satisfied_iff placement branch depth right output).mp
      rightMatch
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases inside : bit < depth.val
  · calc
      left.testBit bit = output (placement.data ⟨bit, by omega⟩) :=
        (leftBits ⟨bit, inside⟩).symm
      _ = right.testBit bit := rightBits ⟨bit, inside⟩
  · have depthLe : depth.val ≤ bit := Nat.le_of_not_gt inside
    have leftAtBit : left < 2 ^ bit :=
      lt_of_lt_of_le leftBound
        (Nat.pow_le_pow_right (by decide) depthLe)
    have rightAtBit : right < 2 ^ bit :=
      lt_of_lt_of_le rightBound
        (Nat.pow_le_pow_right (by decide) depthLe)
    rw [Nat.testBit_eq_false_of_lt leftAtBit,
      Nat.testBit_eq_false_of_lt rightAtBit]

theorem SparseInitial.activePattern_bound
    {p : QParameters} (input : SparseInitial p)
    (depth pattern : Nat) (active : pattern ∈ input.activePatterns depth) :
    pattern < 2 ^ depth := by
  unfold SparseInitial.activePatterns at active
  rw [List.mem_eraseDups] at active
  obtain ⟨configuration, _, rfl⟩ := List.mem_map.mp active
  exact prefixPattern_lt configuration depth

theorem SparseInitial.activePattern_of_branchMass_pos
    {p : QParameters} (input : SparseInitial p)
    (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth)
    (massPos : 0 < input.branchMass depth pattern) :
    pattern ∈ input.activePatterns depth := by
  by_contra absent
  have massZero :=
    input.branchMass_eq_zero_of_not_mem_activePatterns depth pattern
      patternBound absent
  simp [massZero] at massPos

private theorem nodup_eraseDups_nat (items : List Nat) :
    items.eraseDups.Nodup := by
  have go : ∀ n : Nat, ∀ values : List Nat,
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

theorem SparseInitial.activePatterns_nodup
    {p : QParameters} (input : SparseInitial p) (depth : Nat) :
    (input.activePatterns depth).Nodup := by
  exact nodup_eraseDups_nat _

private theorem nodup_list_split_at
    {α : Type} [DecidableEq α] (items : List α)
    (nodup : items.Nodup) (item : α) (member : item ∈ items) :
    ∃ before after, items = before ++ item :: after ∧
      item ∉ before ∧ item ∉ after := by
  induction items with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      have headNotTail := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases same : item = head
      · subst head
        exact ⟨[], tail, rfl, by simp, headNotTail⟩
      · have tailMember : item ∈ tail := by
          rcases List.mem_cons.mp member with headEq | tailMem
          · exact (same headEq).elim
          · exact tailMem
        obtain ⟨before, after, split, notBefore, notAfter⟩ :=
          inductionHypothesis tailNodup tailMember
        refine ⟨head :: before, after, ?_, ?_, notAfter⟩
        · simp [split]
        · simp [same, notBefore]

theorem SparseInitial.activePatterns_split
    {p : QParameters} (input : SparseInitial p)
    (depth pattern : Nat) (member : pattern ∈ input.activePatterns depth) :
    ∃ before after,
      input.activePatterns depth = before ++ pattern :: after ∧
      pattern ∉ before ∧ pattern ∉ after :=
  nodup_list_split_at _ (SparseInitial.activePatterns_nodup input depth)
    pattern member

def prefixRotationInstructionWhen
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    CleanRotationInstruction qubits placement.scratch where
  controls := (branch, true) :: prefixControlsAt placement depth pattern
  target := placement.data depth
  angle := input.branchAngle depth.val pattern
  enoughScratch := prefixControlsAtWhen_enoughScratch placement branch facts
    depth pattern
  layoutNodup := prefixControlsAtWhen_layoutNodup placement branch facts
    depth pattern

/-- At a fixed depth, the actual sparse prefix circuit has precisely one
local `Ry` action on an output whose active prefix matches. -/
theorem SparseInitial.magnitudeDepth_single_active_output
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (member : pattern ∈ input.activePatterns depth.val)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (enabled : boolControlsSatisfied
      ((branch, true) :: prefixControlsAt placement depth pattern)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.activePatterns depth.val).map fun candidate =>
              Circuit.boolMultiControlledRy
                ((branch, true) :: prefixControlsAt placement depth candidate)
                placement.scratch (placement.data depth)
                (input.branchAngle depth.val candidate))) state output =
      ∑ inputBit : Bool,
        localRy (input.branchAngle depth.val pattern).uniformValue
          (output (placement.data depth)) inputBit *
          state (replaceQubitWire output (placement.data depth) inputBit) := by
  obtain ⟨before, after, split, notBefore, notAfter⟩ :=
    SparseInitial.activePatterns_split input depth.val pattern member
  let instruction : Nat → CleanRotationInstruction qubits placement.scratch :=
    prefixRotationInstructionWhen input placement branch facts depth
  have disabledOfDifferent : ∀ candidate ∈ input.activePatterns depth.val,
      candidate ≠ pattern →
        boolControlsSatisfied
          ((branch, true) :: prefixControlsAt placement depth candidate)
          output = false := by
    intro candidate candidateMember different
    cases condition : boolControlsSatisfied
        ((branch, true) :: prefixControlsAt placement depth candidate)
        output with
    | false => rfl
    | true =>
        have same := prefixControlsAtWhen_unique placement branch depth
          candidate pattern
          (SparseInitial.activePattern_bound input depth.val candidate
            candidateMember)
          (SparseInitial.activePattern_bound input depth.val pattern member)
          output condition enabled
        exact (different same).elim
  have sameTargetBefore : ∀ current ∈ before.map instruction,
      current.target = (instruction pattern).target := by
    intro current currentMember
    rcases List.mem_map.mp currentMember with ⟨candidate, _, rfl⟩
    rfl
  have beforeDisabled : ∀ current ∈ before.map instruction,
      boolControlsSatisfied current.controls output = false := by
    intro current currentMember
    rcases List.mem_map.mp currentMember with ⟨candidate, candidateBefore, rfl⟩
    dsimp only [instruction, prefixRotationInstructionWhen]
    apply disabledOfDifferent candidate
    · rw [split]
      exact List.mem_append.mpr (Or.inl candidateBefore)
    · intro same
      subst candidate
      exact notBefore candidateBefore
  have afterDisabled : ∀ current ∈ after.map instruction,
      boolControlsSatisfied current.controls output = false := by
    intro current currentMember
    rcases List.mem_map.mp currentMember with ⟨candidate, candidateAfter, rfl⟩
    dsimp only [instruction, prefixRotationInstructionWhen]
    apply disabledOfDifferent candidate
    · rw [split]
      exact List.mem_append.mpr (Or.inr (by simp [candidateAfter]))
    · intro same
      subst candidate
      exact notAfter candidateAfter
  have selectedEnabled :
      boolControlsSatisfied (instruction pattern).controls output = true :=
    enabled
  have result := compiledCleanRotations_single_active_output
    placement.scratch (before.map instruction) (after.map instruction)
    (instruction pattern) sameTargetBefore state support output
    beforeDisabled selectedEnabled afterDisabled
  rw [split]
  simpa only [List.map_append, List.map_cons, List.map_map, Function.comp_def,
    instruction, CleanRotationInstruction.compile,
    prefixRotationInstructionWhen] using result

theorem localRy_on_target_zero_state
    {qubits : Nat} (target : Fin qubits) (angle : ℝ)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (targetZero : ∀ basis, basis target = true → state basis = 0)
    (output : QubitBasis qubits) :
    (∑ inputBit : Bool,
        localRy angle (output target) inputBit *
          state (replaceQubitWire output target inputBit)) =
      (if output target then (Real.sin (angle / 2) : ℂ)
        else (Real.cos (angle / 2) : ℂ)) *
        state (replaceQubitWire output target false) := by
  have trueZero :
      state (replaceQubitWire output target true) = 0 := by
    apply targetZero
    simp [replaceQubitWire]
  cases outputBit : output target <;>
    simp [localRy, trueZero]

/-- The selected prefix rotation transports a zero target bit with the
cosine/sine weights encoded by the theoretical branch masses. -/
theorem SparseInitial.magnitudeDepth_single_active_of_target_zero
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (member : pattern ∈ input.activePatterns depth.val)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero placement.scratch state)
    (targetZero : ∀ basis, basis (placement.data depth) = true →
      state basis = 0)
    (output : QubitBasis qubits)
    (enabled : boolControlsSatisfied
      ((branch, true) :: prefixControlsAt placement depth pattern)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.activePatterns depth.val).map fun candidate =>
              Circuit.boolMultiControlledRy
                ((branch, true) :: prefixControlsAt placement depth candidate)
                placement.scratch (placement.data depth)
                (input.branchAngle depth.val candidate))) state output =
      (if output (placement.data depth) then
        (Real.sin ((input.branchAngle depth.val pattern).uniformValue / 2) : ℂ)
      else
        (Real.cos ((input.branchAngle depth.val pattern).uniformValue / 2) : ℂ)) *
        state (replaceQubitWire output (placement.data depth) false) := by
  rw [SparseInitial.magnitudeDepth_single_active_output input placement branch
    facts depth pattern member state support output enabled]
  exact localRy_on_target_zero_state (placement.data depth)
    (input.branchAngle depth.val pattern).uniformValue state targetZero output

/-- The two amplitudes of one active prefix layer are the square roots of
the corresponding child-to-parent mass ratios. -/
theorem SparseInitial.magnitudeDepth_mass_ratio
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (member : pattern ∈ input.activePatterns depth.val)
    (parentPos : 0 < input.branchMass depth.val pattern)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero placement.scratch state)
    (targetZero : ∀ basis, basis (placement.data depth) = true →
      state basis = 0)
    (output : QubitBasis qubits)
    (enabled : boolControlsSatisfied
      ((branch, true) :: prefixControlsAt placement depth pattern)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.activePatterns depth.val).map fun candidate =>
              Circuit.boolMultiControlledRy
                ((branch, true) :: prefixControlsAt placement depth candidate)
                placement.scratch (placement.data depth)
                (input.branchAngle depth.val candidate))) state output =
      (if output (placement.data depth) then
        (Real.sqrt
          (((input.branchMass (depth.val + 1)
              (pattern + 2 ^ depth.val) : ℚ) : ℝ) /
            ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ)
      else
        (Real.sqrt
          (((input.branchMass (depth.val + 1) pattern : ℚ) : ℝ) /
            ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ)) *
        state (replaceQubitWire output (placement.data depth) false) := by
  rw [SparseInitial.magnitudeDepth_single_active_of_target_zero input
    placement branch facts depth pattern member state support targetZero output
    enabled]
  by_cases outputBit : output (placement.data depth) = true
  · rw [if_pos outputBit, if_pos outputBit]
    rw [input.sin_half_branchAngle_eq_right_mass depth.val pattern
      (SparseInitial.activePattern_bound input depth.val pattern member)
      parentPos]
  · have falseBit : output (placement.data depth) = false := by
      cases value : output (placement.data depth) <;> simp_all
    rw [if_neg outputBit, if_neg outputBit]
    rw [input.cos_half_branchAngle depth.val pattern parentPos]

/-- The proof-local prefix circuit exposes the execution-order induction on
depth without changing the shared circuit builder. -/
def SparseInitial.magnitudeLayerAtWhen
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (depth : Fin p.systemWidth) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence <|
    (input.activePatterns depth.val).map fun pattern =>
      Circuit.boolMultiControlledRy
        ((branch, true) :: prefixControlsAt placement depth pattern)
        placement.scratch (placement.data depth)
        (input.branchAngle depth.val pattern)

def SparseInitial.magnitudePrefixAtWhen
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (count : Nat) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence <|
    ((List.finRange p.systemWidth).take count).map fun depth =>
      SparseInitial.magnitudeLayerAtWhen input placement branch depth

private theorem sequence_append_last_apply
    {qubits : Nat}
    (circuits : List (Circuit (PrimitiveGate qubits)))
    (last : Circuit (PrimitiveGate qubits))
    (state : VerifiedCircuitCore.State (QubitBasis qubits)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (circuits ++ [last]))) state =
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) last)
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (Circuit.sequence circuits)) state) := by
  have split :
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (circuits ++ [last])) =
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) last *
          Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (Circuit.sequence circuits) := by
    rw [Circuit.denote_sequence_eq_operatorSequence, List.map_append,
      operatorSequence_append,
      ← Circuit.denote_sequence_eq_operatorSequence]
    simp [Circuit.denote_sequence_eq_operatorSequence, operatorSequence]
  rw [split, applyOperator_mul]

theorem SparseInitial.magnitudePrefixAtWhen_step
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (depth : Fin p.systemWidth)
    (state : VerifiedCircuitCore.State (QubitBasis qubits)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            (depth.val + 1)))
        state =
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudeLayerAtWhen input placement branch depth))
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (SparseInitial.magnitudePrefixAtWhen input placement branch
              depth.val)) state) := by
  unfold SparseInitial.magnitudePrefixAtWhen
  rw [List.take_succ_eq_append_getElem
    (by simpa only [List.length_finRange] using depth.isLt)]
  simp only [List.getElem_finRange, List.map_append, List.map_singleton]
  exact sequence_append_last_apply _ _ state

theorem SparseInitial.magnitudePrefixAtWhen_full
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) :
    SparseInitial.magnitudePrefixAtWhen input placement branch p.systemWidth =
      Circuit.sequence
        ((List.finRange p.systemWidth).map fun depth =>
          SparseInitial.magnitudeLayerAtWhen input placement branch depth) := by
  unfold SparseInitial.magnitudePrefixAtWhen
  have htake : (List.finRange p.systemWidth).take p.systemWidth =
      List.finRange p.systemWidth := by
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange p.systemWidth))
  rw [htake]

private theorem finRange_take_member_lt
    (width count : Nat) (index : Fin width)
    (member : index ∈ (List.finRange width).take count) :
    index.val < count := by
  obtain ⟨position, positionBound, positionEq⟩ :=
    List.mem_take_iff_getElem.mp member
  have positionCount : position < count :=
    lt_of_lt_of_le positionBound (Nat.min_le_left _ _)
  have sameValue : position = index.val := by
    have equal := congrArg Fin.val positionEq
    simpa only [List.getElem_finRange, Fin.val_cast] using equal
  omega

theorem compiledNestedCleanRotations_preserve_scratchZero
    {qubits : Nat} (scratches : List (Fin qubits))
    (groups : List (List (CleanRotationInstruction qubits scratches)))
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state) :
    SupportedOnScratchZero scratches
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (groups.map fun group =>
            Circuit.sequence (group.map CleanRotationInstruction.compile))))
        state) := by
  induction groups generalizing state with
  | nil =>
      simpa [Circuit.sequence, Circuit.denote, applyOperator] using support
  | cons group rest inductionHypothesis =>
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      exact inductionHypothesis _
        (compiledCleanRotations_preserve_scratchZero scratches group state
          support)

theorem compiledNestedCleanRotations_preserve_false_wire
    {qubits : Nat} (scratches : List (Fin qubits))
    (groups : List (List (CleanRotationInstruction qubits scratches)))
    (wire : Fin qubits)
    (wireOutsideTargets : ∀ group ∈ groups, ∀ instruction ∈ group,
      wire ≠ instruction.target)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (supportWire : ∀ basis, basis wire = true → state basis = 0) :
    ∀ output, output wire = true →
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (groups.map fun group =>
            Circuit.sequence (group.map CleanRotationInstruction.compile))))
        state output = 0 := by
  induction groups generalizing state with
  | nil =>
      simpa [Circuit.sequence, Circuit.denote, applyOperator] using supportWire
  | cons group rest inductionHypothesis =>
      have groupOutside : ∀ instruction ∈ group,
          wire ≠ instruction.target := by
        intro instruction member
        exact wireOutsideTargets group (by simp) instruction member
      have restOutside : ∀ next ∈ rest, ∀ instruction ∈ next,
          wire ≠ instruction.target := by
        intro next member instruction instructionMember
        exact wireOutsideTargets next (by simp [member]) instruction
          instructionMember
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have nextScratch : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (Circuit.sequence
                (group.map CleanRotationInstruction.compile))) state) :=
        compiledCleanRotations_preserve_scratchZero scratches group state
          supportScratch
      have nextWire : ∀ basis, basis wire = true →
          applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (Circuit.sequence
                (group.map CleanRotationInstruction.compile))) state basis = 0 :=
        compiledCleanRotations_preserve_false_wire scratches group wire
          groupOutside state supportScratch supportWire
      exact inductionHypothesis restOutside _ nextScratch nextWire

theorem SparseInitial.magnitudePrefixAtWhen_preserves_scratchZero
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count : Nat)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero placement.scratch state) :
    SupportedOnScratchZero placement.scratch
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch count))
        state) := by
  let groups : List (List (CleanRotationInstruction qubits placement.scratch)) :=
    ((List.finRange p.systemWidth).take count).map fun depth =>
      (input.activePatterns depth.val).map fun pattern =>
        prefixRotationInstructionWhen input placement branch facts depth pattern
  simpa only [SparseInitial.magnitudePrefixAtWhen,
    SparseInitial.magnitudeLayerAtWhen, groups, List.map_map,
    Function.comp_def, CleanRotationInstruction.compile,
    prefixRotationInstructionWhen] using
    compiledNestedCleanRotations_preserve_scratchZero
      placement.scratch groups state support

theorem SparseInitial.magnitudePrefixAtWhen_preserves_false_wire
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (count : Nat) (wire : Fin qubits)
    (wireOutsideTargets : ∀ depth ∈ (List.finRange p.systemWidth).take count,
      wire ≠ placement.data depth)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportWire : ∀ basis, basis wire = true → state basis = 0) :
    ∀ output, output wire = true →
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch count))
        state output = 0 := by
  let groups : List (List (CleanRotationInstruction qubits placement.scratch)) :=
    ((List.finRange p.systemWidth).take count).map fun depth =>
      (input.activePatterns depth.val).map fun pattern =>
        prefixRotationInstructionWhen input placement branch facts depth pattern
  have outside : ∀ group ∈ groups, ∀ instruction ∈ group,
      wire ≠ instruction.target := by
    intro group groupMember instruction instructionMember
    dsimp [groups] at groupMember
    rcases List.mem_map.mp groupMember with ⟨depth, depthMember, rfl⟩
    rcases List.mem_map.mp instructionMember with ⟨pattern, _, rfl⟩
    exact wireOutsideTargets depth depthMember
  simpa only [SparseInitial.magnitudePrefixAtWhen,
    SparseInitial.magnitudeLayerAtWhen, groups, List.map_map,
    Function.comp_def, CleanRotationInstruction.compile,
    prefixRotationInstructionWhen] using
    compiledNestedCleanRotations_preserve_false_wire
      placement.scratch groups wire outside state supportScratch supportWire

theorem SparseInitial.magnitudePrefixAtWhen_current_target_zero
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportCurrent : ∀ basis,
      basis (placement.data depth) = true → state basis = 0) :
    ∀ output, output (placement.data depth) = true →
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            depth.val)) state output = 0 := by
  apply SparseInitial.magnitudePrefixAtWhen_preserves_false_wire
    input placement branch facts depth.val (placement.data depth)
    ?_ state supportScratch supportCurrent
  intro earlier earlierMember equalWire
  have earlierLt := finRange_take_member_lt p.systemWidth depth.val earlier
    earlierMember
  have sameDepth := facts.dataInjective equalWire
  have equalValue := congrArg Fin.val sameDepth
  omega

theorem SparseInitial.magnitudeLayerAtWhen_preserves_zero_fiber
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (fiberZero : ∀ value : Bool,
      state (replaceQubitWire output (placement.data depth) value) = 0) :
    ∀ value : Bool,
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudeLayerAtWhen input placement branch depth))
        state (replaceQubitWire output (placement.data depth) value) = 0 := by
  let instructions : List
      (CleanRotationInstruction qubits placement.scratch) :=
    (input.activePatterns depth.val).map fun pattern =>
      prefixRotationInstructionWhen input placement branch facts depth pattern
  have sameTarget : ∀ instruction ∈ instructions,
      instruction.target = placement.data depth := by
    intro instruction member
    rcases List.mem_map.mp member with ⟨pattern, _, rfl⟩
    rfl
  simpa only [SparseInitial.magnitudeLayerAtWhen, instructions,
    CleanRotationInstruction.compile, prefixRotationInstructionWhen,
    List.map_map, Function.comp_def] using
    compiledCleanRotations_preserves_zero_fiber placement.scratch
      instructions (placement.data depth) sameTarget state supportScratch output
      fiberZero

/-- One more layer of the theoretical preparation multiplies the already
prepared prefix amplitude by its child-to-parent mass ratio. This theorem is
about the common circuit's local semantics, not a numerical accuracy claim. -/
theorem SparseInitial.magnitudePrefixAtWhen_step_mass_ratio
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (member : pattern ∈ input.activePatterns depth.val)
    (parentPos : 0 < input.branchMass depth.val pattern)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportCurrent : ∀ basis,
      basis (placement.data depth) = true → state basis = 0)
    (output : QubitBasis qubits)
    (enabled : boolControlsSatisfied
      ((branch, true) :: prefixControlsAt placement depth pattern)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            (depth.val + 1))) state output =
      (if output (placement.data depth) then
        (Real.sqrt
          (((input.branchMass (depth.val + 1)
              (pattern + 2 ^ depth.val) : ℚ) : ℝ) /
            ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ)
      else
        (Real.sqrt
          (((input.branchMass (depth.val + 1) pattern : ℚ) : ℝ) /
            ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ)) *
        applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (SparseInitial.magnitudePrefixAtWhen input placement branch
              depth.val)) state
          (replaceQubitWire output (placement.data depth) false) := by
  rw [SparseInitial.magnitudePrefixAtWhen_step]
  have priorScratch :=
    SparseInitial.magnitudePrefixAtWhen_preserves_scratchZero
      input placement branch facts depth.val state supportScratch
  have priorCurrent :=
    SparseInitial.magnitudePrefixAtWhen_current_target_zero
      input placement branch facts depth state supportScratch supportCurrent
  simpa only [SparseInitial.magnitudeLayerAtWhen] using
    SparseInitial.magnitudeDepth_mass_ratio input placement branch facts depth
      pattern member parentPos
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            depth.val)) state)
      priorScratch priorCurrent output enabled

/-- The scalar cancellation used when child mass is propagated through one
more theoretical preparation layer. -/
private theorem sqrt_child_parent_mul_parent_root
    (child parent root : ℚ)
    (childNonneg : 0 ≤ child) (parentPos : 0 < parent)
    (rootPos : 0 < root) :
    (Real.sqrt (((child : ℚ) : ℝ) / ((parent : ℚ) : ℝ)) : ℂ) *
        (Real.sqrt (((parent : ℚ) : ℝ) / ((root : ℚ) : ℝ)) : ℂ) =
      (Real.sqrt (((child : ℚ) : ℝ) / ((root : ℚ) : ℝ)) : ℂ) := by
  have childNonnegReal : (0 : ℝ) ≤ (child : ℝ) := by
    exact_mod_cast childNonneg
  have parentPosReal : (0 : ℝ) < (parent : ℝ) := by
    exact_mod_cast parentPos
  have rootPosReal : (0 : ℝ) < (root : ℝ) := by
    exact_mod_cast rootPos
  have scalar :
      Real.sqrt ((child : ℝ) / (parent : ℝ)) *
          Real.sqrt ((parent : ℝ) / (root : ℝ)) =
        Real.sqrt ((child : ℝ) / (root : ℝ)) := by
    calc
      _ = Real.sqrt (((child : ℝ) / (parent : ℝ)) *
            ((parent : ℝ) / (root : ℝ))) :=
        (Real.sqrt_mul (div_nonneg childNonnegReal
          (le_of_lt parentPosReal)) _).symm
      _ = Real.sqrt ((child : ℝ) / (root : ℝ)) := by
        congr 1
        field_simp
  exact_mod_cast scalar

/-- The actual next layer sends one positive-mass parent prefix to the two
canonical child bases with the expected conditional mass coefficients. -/
theorem SparseInitial.magnitudePrefixAtWhen_positive_children
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val)
    (parentPos : 0 < input.branchMass depth.val pattern)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportCurrent : ∀ basis,
      basis (placement.data depth) = true → state basis = 0) :
    let before := applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (SparseInitial.magnitudePrefixAtWhen input placement branch depth.val))
      state
    let after := applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (SparseInitial.magnitudePrefixAtWhen input placement branch
          (depth.val + 1))) state
    after (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        pattern) =
        (Real.sqrt
          (((input.branchMass (depth.val + 1) pattern : ℚ) : ℝ) /
            ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ) *
          before (SparseInitial.prefixBasis placement branch facts depth.val
            pattern) ∧
      after (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        (pattern + 2 ^ depth.val)) =
        (Real.sqrt
          (((input.branchMass (depth.val + 1)
              (pattern + 2 ^ depth.val) : ℚ) : ℝ) /
            ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ) *
          before (SparseInitial.prefixBasis placement branch facts depth.val
            pattern) := by
  dsimp only
  have member := SparseInitial.activePattern_of_branchMass_pos input
    depth.val pattern patternBound parentPos
  constructor
  · have leftBit :
        SparseInitial.prefixBasis placement branch facts (depth.val + 1)
            pattern (placement.data depth) = false := by
      rw [SparseInitial.prefixBasis_data]
      simp [Nat.testBit_lt_two_pow patternBound]
    have step := SparseInitial.magnitudePrefixAtWhen_step_mass_ratio input
      placement branch facts depth pattern member parentPos state supportScratch
      supportCurrent
      (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        pattern)
      (SparseInitial.prefixBasis_left_child_controls placement branch facts
        depth pattern patternBound)
    simpa [leftBit,
      SparseInitial.prefixBasis_left_child_parent placement branch facts depth
        pattern patternBound] using step
  · have rightBit :
        SparseInitial.prefixBasis placement branch facts (depth.val + 1)
            (pattern + 2 ^ depth.val) (placement.data depth) = true := by
      rw [SparseInitial.prefixBasis_data]
      simp [testBit_add_pow_at depth.val pattern patternBound]
    have step := SparseInitial.magnitudePrefixAtWhen_step_mass_ratio input
      placement branch facts depth pattern member parentPos state supportScratch
      supportCurrent
      (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        (pattern + 2 ^ depth.val))
      (SparseInitial.prefixBasis_right_child_controls placement branch facts
        depth pattern patternBound)
    simpa [rightBit,
      SparseInitial.prefixBasis_right_child_parent placement branch facts depth
        pattern patternBound] using step

/-- A zero-amplitude parent prefix cannot acquire amplitude in either canonical
child basis. This is a local fact used for the theoretical `bPlus` proof. -/
theorem SparseInitial.magnitudePrefixAtWhen_zero_children
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportCurrent : ∀ basis,
      basis (placement.data depth) = true → state basis = 0)
    (parentZero :
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            depth.val)) state
        (SparseInitial.prefixBasis placement branch facts depth.val pattern) =
          0) :
    let after := applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (SparseInitial.magnitudePrefixAtWhen input placement branch
          (depth.val + 1))) state
    after (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        pattern) = 0 ∧
      after (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        (pattern + 2 ^ depth.val)) = 0 := by
  dsimp only
  let prior := applyOperator
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (SparseInitial.magnitudePrefixAtWhen input placement branch depth.val))
    state
  have priorScratch : SupportedOnScratchZero placement.scratch prior :=
    SparseInitial.magnitudePrefixAtWhen_preserves_scratchZero
      input placement branch facts depth.val state supportScratch
  have priorCurrent : ∀ basis,
      basis (placement.data depth) = true → prior basis = 0 :=
    SparseInitial.magnitudePrefixAtWhen_current_target_zero
      input placement branch facts depth state supportScratch supportCurrent
  have zeroFiber (output : QubitBasis qubits)
      (parentEq : replaceQubitWire output (placement.data depth) false =
        SparseInitial.prefixBasis placement branch facts depth.val pattern) :
      ∀ value : Bool,
        prior (replaceQubitWire output (placement.data depth) value) = 0 := by
    intro value
    cases value with
    | false => simpa only [parentEq, prior] using parentZero
    | true =>
        exact priorCurrent _ (replaceQubitWire_target output
          (placement.data depth) true)
  constructor
  · let output := SparseInitial.prefixBasis placement branch facts
      (depth.val + 1) pattern
    have outputBit : output (placement.data depth) = false := by
      dsimp only [output]
      rw [SparseInitial.prefixBasis_data]
      simp [Nat.testBit_lt_two_pow patternBound]
    have outputParent : replaceQubitWire output (placement.data depth) false =
        SparseInitial.prefixBasis placement branch facts depth.val pattern :=
      SparseInitial.prefixBasis_left_child_parent placement branch facts depth
        pattern patternBound
    have zero := SparseInitial.magnitudeLayerAtWhen_preserves_zero_fiber
      input placement branch facts depth prior priorScratch output
      (zeroFiber output outputParent) false
    have outputSelf : replaceQubitWire output (placement.data depth) false =
        output := by
      simpa [outputBit] using replaceQubitWire_self output
        (placement.data depth)
    rw [SparseInitial.magnitudePrefixAtWhen_step]
    simpa only [output, prior, outputSelf] using zero
  · let output := SparseInitial.prefixBasis placement branch facts
      (depth.val + 1) (pattern + 2 ^ depth.val)
    have outputBit : output (placement.data depth) = true := by
      dsimp only [output]
      rw [SparseInitial.prefixBasis_data]
      simp [testBit_add_pow_at depth.val pattern patternBound]
    have outputParent : replaceQubitWire output (placement.data depth) false =
        SparseInitial.prefixBasis placement branch facts depth.val pattern :=
      SparseInitial.prefixBasis_right_child_parent placement branch facts depth
        pattern patternBound
    have zero := SparseInitial.magnitudeLayerAtWhen_preserves_zero_fiber
      input placement branch facts depth prior priorScratch output
      (zeroFiber output outputParent) true
    have outputSelf : replaceQubitWire output (placement.data depth) true =
        output := by
      simpa [outputBit] using replaceQubitWire_self output
        (placement.data depth)
    rw [SparseInitial.magnitudePrefixAtWhen_step]
    simpa only [output, prior, outputSelf] using zero

/-- The two child amplitudes satisfy the square-root mass invariant whenever
the parent does. This combines the positive- and zero-mass cases without any
claim about a numerical QSP provider. -/
theorem SparseInitial.magnitudePrefixAtWhen_children_mass_amplitude
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (depth : Fin p.systemWidth) (pattern : Nat)
    (patternBound : pattern < 2 ^ depth.val)
    (rootMass : ℚ) (rootPos : 0 < rootMass) (initialAmplitude : ℂ)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportCurrent : ∀ basis,
      basis (placement.data depth) = true → state basis = 0)
    (parentAmplitude :
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            depth.val)) state
        (SparseInitial.prefixBasis placement branch facts depth.val pattern) =
      (Real.sqrt
        (((input.branchMass depth.val pattern : ℚ) : ℝ) /
          ((rootMass : ℚ) : ℝ)) : ℂ) * initialAmplitude) :
    let after := applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (SparseInitial.magnitudePrefixAtWhen input placement branch
          (depth.val + 1))) state
    after (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        pattern) =
        (Real.sqrt
          (((input.branchMass (depth.val + 1) pattern : ℚ) : ℝ) /
            ((rootMass : ℚ) : ℝ)) : ℂ) * initialAmplitude ∧
      after (SparseInitial.prefixBasis placement branch facts (depth.val + 1)
        (pattern + 2 ^ depth.val)) =
        (Real.sqrt
          (((input.branchMass (depth.val + 1)
              (pattern + 2 ^ depth.val) : ℚ) : ℝ) /
            ((rootMass : ℚ) : ℝ)) : ℂ) * initialAmplitude := by
  dsimp only
  by_cases parentPos : 0 < input.branchMass depth.val pattern
  · obtain ⟨leftStep, rightStep⟩ :=
      SparseInitial.magnitudePrefixAtWhen_positive_children input placement
        branch facts depth pattern patternBound parentPos state supportScratch
        supportCurrent
    constructor
    · calc
        _ =
            (Real.sqrt
              (((input.branchMass (depth.val + 1) pattern : ℚ) : ℝ) /
                ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ) *
              applyOperator
                (Circuit.denote
                  (primitiveGateOperatorWithSymbols (fun _ => 0))
                  (SparseInitial.magnitudePrefixAtWhen input placement branch
                    depth.val)) state
                (SparseInitial.prefixBasis placement branch facts depth.val
                  pattern) := leftStep
        _ = _ := by
          rw [parentAmplitude, ← mul_assoc,
            sqrt_child_parent_mul_parent_root
              (input.branchMass (depth.val + 1) pattern)
              (input.branchMass depth.val pattern) rootMass
              (input.branchMass_nonneg _ _) parentPos rootPos]
    · calc
        _ =
            (Real.sqrt
              (((input.branchMass (depth.val + 1)
                  (pattern + 2 ^ depth.val) : ℚ) : ℝ) /
                ((input.branchMass depth.val pattern : ℚ) : ℝ)) : ℂ) *
              applyOperator
                (Circuit.denote
                  (primitiveGateOperatorWithSymbols (fun _ => 0))
                  (SparseInitial.magnitudePrefixAtWhen input placement branch
                    depth.val)) state
                (SparseInitial.prefixBasis placement branch facts depth.val
                  pattern) := rightStep
        _ = _ := by
          rw [parentAmplitude, ← mul_assoc,
            sqrt_child_parent_mul_parent_root
              (input.branchMass (depth.val + 1)
                (pattern + 2 ^ depth.val))
              (input.branchMass depth.val pattern) rootMass
              (input.branchMass_nonneg _ _) parentPos rootPos]
  · have parentZero : input.branchMass depth.val pattern = 0 :=
      le_antisymm (le_of_not_gt parentPos)
        (input.branchMass_nonneg _ _)
    have childZero := input.branchMass_children_zero_of_parent_zero
      depth.val pattern patternBound parentZero
    have priorZero :
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            depth.val)) state
        (SparseInitial.prefixBasis placement branch facts depth.val pattern) =
          0 := by
      simpa [parentZero] using parentAmplitude
    obtain ⟨leftZero, rightZero⟩ :=
      SparseInitial.magnitudePrefixAtWhen_zero_children input placement
        branch facts depth pattern patternBound state supportScratch
        supportCurrent priorZero
    constructor
    · simpa [childZero.1] using leftZero
    · simpa [childZero.2] using rightZero

/-- Prefix amplitudes after each layer follow the square-root branch masses
from one canonical starting basis. This is an internal preparation lemma for
the theoretical branch, independent of any numerical phase provider. -/
theorem SparseInitial.magnitudePrefixAtWhen_canonical_amplitude
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportData : ∀ depth : Fin p.systemWidth, ∀ basis,
      basis (placement.data depth) = true → state basis = 0)
    (rootPos : 0 < input.branchMass 0 0) (initialAmplitude : ℂ)
    (initialBasis :
      state (SparseInitial.prefixBasis placement branch facts 0 0) =
        initialAmplitude) :
    ∀ count : Nat, count ≤ p.systemWidth →
      ∀ pattern : Nat, pattern < 2 ^ count →
        applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (SparseInitial.magnitudePrefixAtWhen input placement branch
              count)) state
          (SparseInitial.prefixBasis placement branch facts count pattern) =
        (Real.sqrt
          (((input.branchMass count pattern : ℚ) : ℝ) /
            ((input.branchMass 0 0 : ℚ) : ℝ)) : ℂ) * initialAmplitude := by
  intro count
  induction count with
  | zero =>
      intro _ pattern patternBound
      have patternZero : pattern = 0 := by
        have bound : pattern < 1 := by simpa using patternBound
        omega
      subst pattern
      have rootNonzero : ((input.branchMass 0 0 : ℚ) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt rootPos)
      simpa [SparseInitial.magnitudePrefixAtWhen, Circuit.sequence,
        Circuit.denote, applyOperator, rootNonzero] using
        initialBasis
  | succ count ih =>
      intro countBound pattern patternBound
      have depthBound : count < p.systemWidth := by omega
      let depth : Fin p.systemWidth := ⟨count, depthBound⟩
      have priorBound : count ≤ p.systemWidth := by omega
      by_cases left : pattern < 2 ^ count
      · have parentAmplitude := ih priorBound pattern left
        have children :=
          SparseInitial.magnitudePrefixAtWhen_children_mass_amplitude
            input placement branch facts depth pattern left
            (input.branchMass 0 0) rootPos initialAmplitude state
            supportScratch (supportData depth) parentAmplitude
        simpa only [depth] using children.1
      · have lower : 2 ^ count ≤ pattern := le_of_not_gt left
        let parent := pattern - 2 ^ count
        have decomposition : pattern = parent + 2 ^ count := by
          exact (Nat.sub_add_cancel lower).symm
        have parentBound : parent < 2 ^ count := by
          have expanded : 2 ^ (count + 1) = 2 ^ count * 2 := by
            rw [pow_succ]
          omega
        have parentAmplitude := ih priorBound parent parentBound
        have children :=
          SparseInitial.magnitudePrefixAtWhen_children_mass_amplitude
            input placement branch facts depth parent parentBound
            (input.branchMass 0 0) rootPos initialAmplitude state
            supportScratch (supportData depth) parentAmplitude
        simpa only [depth, decomposition] using children.2

/-- The canonical branch-true basis ket has the clean and zero-data support
needed by the theoretical magnitude-preparation induction. -/
theorem SparseInitial.magnitudePrefixAtWhen_basisKet_amplitude
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (rootPos : 0 < input.branchMass 0 0) :
    ∀ count : Nat, count ≤ p.systemWidth →
      ∀ pattern : Nat, pattern < 2 ^ count →
        applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (SparseInitial.magnitudePrefixAtWhen input placement branch
              count))
          (basisKet
            (SparseInitial.prefixBasis placement branch facts 0 0))
          (SparseInitial.prefixBasis placement branch facts count pattern) =
        (Real.sqrt
          (((input.branchMass count pattern : ℚ) : ℝ) /
            ((input.branchMass 0 0 : ℚ) : ℝ)) : ℂ) := by
  let start := SparseInitial.prefixBasis placement branch facts 0 0
  have supportScratch : SupportedOnScratchZero placement.scratch
      (basisKet start) := by
    intro basis dirty
    obtain ⟨wire, member, trueAt⟩ := dirty
    have startFalse : start wire = false :=
      SparseInitial.prefixBasis_scratch_false placement branch facts
        0 0 wire member
    have different : basis ≠ start := by
      intro equal
      subst basis
      simp [startFalse] at trueAt
    simp [basisKet_apply, different]
  have supportData : ∀ depth : Fin p.systemWidth, ∀ basis,
      basis (placement.data depth) = true → basisKet start basis = 0 := by
    intro depth basis trueAt
    have startFalse : start (placement.data depth) = false := by
      dsimp only [start]
      rw [SparseInitial.prefixBasis_data]
      simp
    have different : basis ≠ start := by
      intro equal
      subst basis
      simp [startFalse] at trueAt
    simp [basisKet_apply, different]
  have initialBasis : basisKet start start = (1 : ℂ) := by simp
  intro count countBound pattern patternBound
  have result := SparseInitial.magnitudePrefixAtWhen_canonical_amplitude
    input placement branch facts (basisKet start) supportScratch supportData
    rootPos 1 initialBasis count countBound pattern patternBound
  simpa only [start, mul_one] using result

theorem compiledNestedCleanRotations_identity_on_false_branch
    {qubits : Nat} (scratches : List (Fin qubits))
    (branch : Fin qubits)
    (groups : List (List (CleanRotationInstruction qubits scratches)))
    (branchControlled : ∀ group ∈ groups, ∀ instruction ∈ group,
      ∃ controls, instruction.controls = (branch, true) :: controls ∧
        branch ≠ instruction.target)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (supportBranch : SupportedOnBranchFalse branch state) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (groups.map fun group =>
            Circuit.sequence (group.map CleanRotationInstruction.compile))))
        state = state := by
  induction groups with
  | nil =>
      simp [Circuit.sequence, Circuit.denote, applyOperator]
  | cons group rest inductionHypothesis =>
      have groupControlled : ∀ instruction ∈ group,
          ∃ controls, instruction.controls = (branch, true) :: controls ∧
            branch ≠ instruction.target := by
        intro instruction member
        exact branchControlled group (by simp) instruction member
      have restControlled : ∀ next ∈ rest, ∀ instruction ∈ next,
          ∃ controls, instruction.controls = (branch, true) :: controls ∧
            branch ≠ instruction.target := by
        intro next member instruction memberInstruction
        exact branchControlled next (by simp [member]) instruction
          memberInstruction
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      rw [compiledCleanRotations_identity_on_false_branch scratches branch
        group groupControlled state supportScratch supportBranch]
      exact inductionHypothesis restControlled

theorem compiledNestedCleanRotations_false_branch_output
    {qubits : Nat} (scratches : List (Fin qubits))
    (branch : Fin qubits)
    (groups : List (List (CleanRotationInstruction qubits scratches)))
    (branchControlled : ∀ group ∈ groups, ∀ instruction ∈ group,
      ∃ controls, instruction.controls = (branch, true) :: controls)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (groups.map fun group =>
            Circuit.sequence (group.map CleanRotationInstruction.compile))))
        state output = state output := by
  induction groups generalizing state with
  | nil =>
      simp [Circuit.sequence, Circuit.denote, applyOperator]
  | cons group rest inductionHypothesis =>
      have groupControlled : ∀ instruction ∈ group,
          ∃ controls, instruction.controls = (branch, true) :: controls := by
        intro instruction member
        exact branchControlled group (by simp) instruction member
      have restControlled : ∀ next ∈ rest, ∀ instruction ∈ next,
          ∃ controls, instruction.controls = (branch, true) :: controls := by
        intro next member instruction memberInstruction
        exact branchControlled next (by simp [member]) instruction
          memberInstruction
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      have nextSupport : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (Circuit.sequence
                (group.map CleanRotationInstruction.compile))) state) :=
        compiledCleanRotations_preserve_scratchZero scratches group state
          supportScratch
      rw [inductionHypothesis restControlled _ nextSupport]
      exact compiledCleanRotations_false_branch_output scratches branch group
        groupControlled state supportScratch output branchFalse

/-- The magnitude stage of the common `bPlus` builder keeps the work bits
clean when instantiated in the theoretical preparation proof.  This is not
an accuracy or target-state theorem for a numerical-provider output. -/
theorem SparseInitial.magnitudeAtWhen_preserves_scratchZero
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero placement.scratch state) :
    SupportedOnScratchZero placement.scratch
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (List.finRange p.systemWidth).map fun depth =>
              Circuit.sequence <|
                (input.activePatterns depth.val).map fun pattern =>
                  Circuit.boolMultiControlledRy
                    ((branch, true) :: prefixControlsAt placement depth pattern)
                    placement.scratch (placement.data depth)
                    (input.branchAngle depth.val pattern)))
        state) := by
  let groups : List (List (CleanRotationInstruction qubits placement.scratch)) :=
    (List.finRange p.systemWidth).map fun depth =>
      (input.activePatterns depth.val).map fun pattern =>
        prefixRotationInstructionWhen input placement branch facts depth pattern
  simpa only [groups, List.map_map, Function.comp_def,
    CleanRotationInstruction.compile, prefixRotationInstructionWhen] using
    compiledNestedCleanRotations_preserve_scratchZero
      placement.scratch groups state support

theorem SparseInitial.magnitudeAtWhen_identity_on_false_branch
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (supportBranch : SupportedOnBranchFalse branch state) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (List.finRange p.systemWidth).map fun depth =>
              Circuit.sequence <|
                (input.activePatterns depth.val).map fun pattern =>
                  Circuit.boolMultiControlledRy
                    ((branch, true) :: prefixControlsAt placement depth pattern)
                    placement.scratch (placement.data depth)
                    (input.branchAngle depth.val pattern)))
        state = state := by
  let groups : List (List (CleanRotationInstruction qubits placement.scratch)) :=
    (List.finRange p.systemWidth).map fun depth =>
      (input.activePatterns depth.val).map fun pattern =>
        prefixRotationInstructionWhen input placement branch facts depth pattern
  have branchControlled : ∀ group ∈ groups, ∀ instruction ∈ group,
      ∃ controls, instruction.controls = (branch, true) :: controls ∧
        branch ≠ instruction.target := by
    intro group memberGroup instruction memberInstruction
    dsimp [groups] at memberGroup
    rcases List.mem_map.mp memberGroup with ⟨depth, _, rfl⟩
    rcases List.mem_map.mp memberInstruction with ⟨pattern, _, rfl⟩
    exact ⟨prefixControlsAt placement depth pattern, rfl,
      facts.branchOutsideData depth⟩
  simpa only [groups, List.map_map, Function.comp_def,
    CleanRotationInstruction.compile, prefixRotationInstructionWhen] using
    compiledNestedCleanRotations_identity_on_false_branch
      placement.scratch branch groups branchControlled state supportScratch
      supportBranch

theorem SparseInitial.magnitudePrefixAtWhen_zeroKet_identity
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            p.systemWidth))
        (basisKet (fun _ => false : QubitBasis qubits)) =
      basisKet (fun _ => false : QubitBasis qubits) := by
  have supportScratch : SupportedOnScratchZero placement.scratch
      (basisKet (fun _ => false : QubitBasis qubits)) := by
    intro basis dirty
    obtain ⟨wire, _, trueAt⟩ := dirty
    have different : basis ≠ (fun _ => false : QubitBasis qubits) := by
      intro equal
      have atWire := congrFun equal wire
      simp [trueAt] at atWire
    simp [basisKet_apply, different]
  have supportBranch : SupportedOnBranchFalse branch
      (basisKet (fun _ => false : QubitBasis qubits)) := by
    intro basis branchTrue
    have different : basis ≠ (fun _ => false : QubitBasis qubits) := by
      intro equal
      have atBranch := congrFun equal branch
      simp [branchTrue] at atBranch
    simp [basisKet_apply, different]
  simpa only [SparseInitial.magnitudePrefixAtWhen_full,
    SparseInitial.magnitudeLayerAtWhen] using
    SparseInitial.magnitudeAtWhen_identity_on_false_branch input placement
      branch facts _ supportScratch supportBranch

theorem SparseInitial.magnitudeAtWhen_false_branch_output
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (List.finRange p.systemWidth).map fun depth =>
              Circuit.sequence <|
                (input.activePatterns depth.val).map fun pattern =>
                  Circuit.boolMultiControlledRy
                    ((branch, true) :: prefixControlsAt placement depth pattern)
                    placement.scratch (placement.data depth)
                    (input.branchAngle depth.val pattern)))
        state output = state output := by
  let groups : List (List (CleanRotationInstruction qubits placement.scratch)) :=
    (List.finRange p.systemWidth).map fun depth =>
      (input.activePatterns depth.val).map fun pattern =>
        prefixRotationInstructionWhen input placement branch facts depth pattern
  have branchControlled : ∀ group ∈ groups, ∀ instruction ∈ group,
      ∃ controls, instruction.controls = (branch, true) :: controls := by
    intro group memberGroup instruction memberInstruction
    dsimp [groups] at memberGroup
    rcases List.mem_map.mp memberGroup with ⟨depth, _, rfl⟩
    rcases List.mem_map.mp memberInstruction with ⟨pattern, _, rfl⟩
    exact ⟨prefixControlsAt placement depth pattern, rfl⟩
  simpa only [groups, List.map_map, Function.comp_def,
    CleanRotationInstruction.compile, prefixRotationInstructionWhen] using
    compiledNestedCleanRotations_false_branch_output placement.scratch branch
      groups branchControlled state supportScratch output branchFalse

/-- The sign stage uses the same clean work register, with a separate phase
target.  Its wire obligations will be instantiated only for the theoretical
`bPlus` connection; no numerical output guarantee is attached. -/
structure SignPlacementFacts {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits) : Prop
    extends BranchPlacementFacts placement branch where
  phaseOutsideData : ∀ bit, placement.phase ≠ placement.data bit
  phaseOutsideScratch : placement.phase ∉ placement.scratch
  phaseOutsideBranch : placement.phase ≠ branch

theorem signRotationAngle_uniformValue :
    (AngleExpr.mul (rationalAngle 2) .pi).uniformValue = 2 * Real.pi := by
  change (rationalAngle 2).uniformValue * Real.pi = 2 * Real.pi
  rw [rationalAngle_uniformValue]
  norm_num

theorem localRy_two_pi_apply (output input : Bool) :
    localRy (2 * Real.pi) output input =
      if output = input then (-1 : ℂ) else 0 := by
  have halfAngle : (2 * Real.pi : ℝ) / 2 = Real.pi := by ring
  cases output <;> cases input <;>
    simp [localRy, halfAngle, Real.cos_pi, Real.sin_pi]

theorem localRy_two_pi_on_state
    {qubits : Nat} (target : Fin qubits)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (output : QubitBasis qubits) :
    (∑ inputBit : Bool,
      localRy (2 * Real.pi) (output target) inputBit *
        state (replaceQubitWire output target inputBit)) =
      -state output := by
  cases targetBit : output target with
  | false =>
      have replaceSelf : replaceQubitWire output target false = output := by
        simpa [targetBit] using replaceQubitWire_self output target
      simp [localRy_two_pi_apply, replaceSelf]
  | true =>
      have replaceSelf : replaceQubitWire output target true = output := by
        simpa [targetBit] using replaceQubitWire_self output target
      simp [localRy_two_pi_apply, replaceSelf]

theorem boolMultiControlledSign_applyOperator
    {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.boolMultiControlledRy controls scratches target
            (.mul (rationalAngle 2) .pi))) state output =
      if boolControlsSatisfied controls output then -state output
      else state output := by
  rw [boolMultiControlledRy_applyOperator controls scratches target
    (.mul (rationalAngle 2) .pi) enoughScratch layoutNodup state
    supportScratch output]
  rw [signRotationAngle_uniformValue]
  split_ifs
  · exact localRy_two_pi_on_state target state output
  · rfl

/-- A sequence of controlled full-turn rotations is diagonal on the clean
work subspace. The factor records the actual matching controls, so the later
configuration-uniqueness proof can identify the sign of the theoretical
initial vector without assuming it. -/
theorem compiledSignRotations_applyOperator
    {qubits : Nat} (scratches : List (Fin qubits))
    (instructions : List (CleanRotationInstruction qubits scratches))
    (signAngles : ∀ instruction ∈ instructions,
      instruction.angle = .mul (rationalAngle 2) .pi)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero scratches state)
    (output : QubitBasis qubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence (instructions.map CleanRotationInstruction.compile)))
        state output =
      ((instructions.map fun instruction =>
        if boolControlsSatisfied instruction.controls output then (-1 : ℂ)
        else 1).prod) * state output := by
  induction instructions generalizing state with
  | nil =>
      simp [Circuit.sequence, Circuit.denote, applyOperator]
  | cons instruction rest inductionHypothesis =>
      have restAngles : ∀ next ∈ rest,
          next.angle = .mul (rationalAngle 2) .pi := by
        intro next member
        exact signAngles next (by simp [member])
      have instructionAngle :
          instruction.angle = .mul (rationalAngle 2) .pi :=
        signAngles instruction (by simp)
      have nextSupport : SupportedOnScratchZero scratches
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              instruction.compile) state) := by
        exact boolMultiControlledRy_preserves_scratchZero
          instruction.controls scratches instruction.target instruction.angle
          instruction.enoughScratch instruction.layoutNodup state supportScratch
      simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
        applyOperator_mul]
      rw [inductionHypothesis restAngles _ nextSupport]
      have firstAction :
          applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                instruction.compile) state output =
            if boolControlsSatisfied instruction.controls output then
              -state output else state output := by
        simpa only [CleanRotationInstruction.compile, instructionAngle] using
          boolMultiControlledSign_applyOperator instruction.controls scratches
            instruction.target instruction.enoughScratch
            instruction.layoutNodup state supportScratch output
      rw [firstAction]
      simp only [List.prod_cons]
      by_cases enabled : boolControlsSatisfied instruction.controls output
      · simp [enabled]
      · simp [enabled]

theorem configurationControlsAtWhen_enoughScratch
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p) :
    ((branch, true) :: configurationControlsAt placement configuration).length ≤
      placement.scratch.length + 1 := by
  simp only [List.length_cons, configurationControlsAt, List.length_map,
    List.length_finRange]
  exact Nat.add_le_add_right facts.scratchLength 1

theorem configurationControlsAtWhen_layoutNodup
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p) :
    ((((branch, true) :: configurationControlsAt placement configuration).map
        Prod.fst) ++ placement.scratch ++ [placement.phase]).Nodup := by
  have dataNodup :
      ((configurationControlsAt placement configuration).map Prod.fst).Nodup := by
    simp only [configurationControlsAt, List.map_map]
    exact List.Nodup.map facts.dataInjective (List.nodup_finRange p.systemWidth)
  have dataScratch :
      ((configurationControlsAt placement configuration).map Prod.fst).Disjoint
        placement.scratch := by
    rw [List.disjoint_left]
    intro wire dataMember scratchMember
    simp only [configurationControlsAt, List.map_map] at dataMember
    rcases List.mem_map.mp dataMember with ⟨bit, _, rfl⟩
    exact facts.dataOutsideScratch bit scratchMember
  have dataPhase : placement.phase ∉
      (configurationControlsAt placement configuration).map Prod.fst := by
    intro member
    simp only [configurationControlsAt, List.map_map] at member
    rcases List.mem_map.mp member with ⟨bit, _, equal⟩
    exact facts.phaseOutsideData bit equal.symm
  have dataScratchNodup :
      ((configurationControlsAt placement configuration).map Prod.fst ++
        placement.scratch).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨dataNodup, facts.scratchNodup, ?_⟩
    intro left leftMember right rightMember equal
    subst right
    exact (List.disjoint_left.mp dataScratch) leftMember rightMember
  have dataScratchPhaseNodup :
      ((configurationControlsAt placement configuration).map Prod.fst ++
        placement.scratch ++ [placement.phase]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨dataScratchNodup, by simp, ?_⟩
    intro wire member phase phaseMember equal
    have phaseEqual : phase = placement.phase := by simpa using phaseMember
    subst phase
    subst wire
    rcases List.mem_append.mp member with dataMember | scratchMember
    · exact dataPhase dataMember
    · exact facts.phaseOutsideScratch scratchMember
  simp only [List.map_cons]
  apply List.nodup_cons.mpr
  constructor
  · intro member
    rcases List.mem_append.mp member with member | phaseMember
    · rcases List.mem_append.mp member with dataMember | scratchMember
      · simp only [configurationControlsAt, List.map_map] at dataMember
        rcases List.mem_map.mp dataMember with ⟨bit, _, equal⟩
        exact facts.branchOutsideData bit equal.symm
      · exact facts.branchOutsideScratch scratchMember
    · have phaseEqual : branch = placement.phase := by simpa using phaseMember
      exact facts.phaseOutsideBranch phaseEqual.symm
  · exact dataScratchPhaseNodup

theorem configurationControlsAtWhen_satisfied_iff
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (configuration : QConfiguration p) (output : QubitBasis qubits) :
    boolControlsSatisfied
        ((branch, true) :: configurationControlsAt placement configuration)
        output = true ↔
      output branch = true ∧
        ∀ bit : Fin p.systemWidth,
          output (placement.data bit) = delimiterEncoding configuration bit := by
  simp [boolControlsSatisfied, configurationControlsAt, List.all_eq_true]

theorem SparseInitial.prefixBasis_configuration_controls
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (configuration : QConfiguration p) :
    boolControlsSatisfied
        ((branch, true) :: configurationControlsAt placement configuration)
        (SparseInitial.prefixBasis placement branch facts p.systemWidth
          (prefixPattern configuration p.systemWidth)) = true := by
  rw [configurationControlsAtWhen_satisfied_iff]
  constructor
  · exact SparseInitial.prefixBasis_branch placement branch facts
      p.systemWidth (prefixPattern configuration p.systemWidth)
  · intro bit
    rw [SparseInitial.prefixBasis_data]
    simp [bit.isLt, prefixPattern_testBit, encodedBit]

theorem configurationControlsAtWhen_unique
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (left right : QConfiguration p) (output : QubitBasis qubits)
    (leftMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement left)
      output = true)
    (rightMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement right)
      output = true) :
    left = right := by
  obtain ⟨_, leftBits⟩ :=
    (configurationControlsAtWhen_satisfied_iff placement branch left output).mp
      leftMatch
  obtain ⟨_, rightBits⟩ :=
    (configurationControlsAtWhen_satisfied_iff placement branch right output).mp
      rightMatch
  apply delimiterEncoding_injective
  funext bit
  exact (leftBits bit).symm.trans (rightBits bit)

theorem SparseInitial.configurationBasis_injective
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch) :
    Function.Injective (fun configuration : QConfiguration p =>
      SparseInitial.prefixBasis placement branch facts p.systemWidth
        (prefixPattern configuration p.systemWidth)) := by
  intro left right equal
  apply configurationControlsAtWhen_unique placement branch left right
    (SparseInitial.prefixBasis placement branch facts p.systemWidth
      (prefixPattern left p.systemWidth))
  · exact SparseInitial.prefixBasis_configuration_controls
      placement branch facts left
  · have rightMatch := SparseInitial.prefixBasis_configuration_controls
      placement branch facts right
    change SparseInitial.prefixBasis placement branch facts p.systemWidth
      (prefixPattern left p.systemWidth) =
        SparseInitial.prefixBasis placement branch facts p.systemWidth
          (prefixPattern right p.systemWidth) at equal
    rw [← equal] at rightMatch
    exact rightMatch

theorem SparseInitial.configurationBasis_ne_zero
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (configuration : QConfiguration p) :
    SparseInitial.prefixBasis placement branch facts p.systemWidth
        (prefixPattern configuration p.systemWidth) ≠
      (fun _ => false : QubitBasis qubits) := by
  intro equal
  have atBranch := congrFun equal branch
  rw [SparseInitial.prefixBasis_branch] at atBranch
  simp at atBranch

theorem signFactor_eq_one_of_ne
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (configuration other : QConfiguration p) (output : QubitBasis qubits)
    (configurationMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true)
    (different : other ≠ configuration) :
    (if boolControlsSatisfied
        ((branch, true) :: configurationControlsAt placement other)
        output then (-1 : ℂ) else 1) = 1 := by
  have otherMismatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement other)
      output = false := by
    cases otherMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement other) output with
    | false => rfl
    | true =>
        exact (different (configurationControlsAtWhen_unique placement branch
          other configuration output otherMatch configurationMatch)).elim
  simp [otherMismatch]

theorem signProduct_eq_one_of_not_mem
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (configuration : QConfiguration p) (output : QubitBasis qubits)
    (configurationMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true)
    (configurations : List (QConfiguration p))
    (absent : configuration ∉ configurations) :
    ((configurations.map fun other =>
      if boolControlsSatisfied
          ((branch, true) :: configurationControlsAt placement other) output
        then (-1 : ℂ) else 1).prod) = 1 := by
  induction configurations with
  | nil => simp
  | cons other rest inductionHypothesis =>
      have otherDifferent : other ≠ configuration := by
        intro equal
        exact absent (by simp [equal])
      have absentRest : configuration ∉ rest := by
        intro member
        exact absent (by simp [member])
      simp only [List.map_cons, List.prod_cons]
      rw [signFactor_eq_one_of_ne placement branch configuration other
        output configurationMatch otherDifferent,
        inductionHypothesis absentRest]
      norm_num

theorem signProduct_eq_if_mem
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits) (branch : Fin qubits)
    (configuration : QConfiguration p) (output : QubitBasis qubits)
    (configurationMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true)
    (configurations : List (QConfiguration p))
    (nodup : configurations.Nodup) :
    ((configurations.map fun other =>
      if boolControlsSatisfied
          ((branch, true) :: configurationControlsAt placement other) output
        then (-1 : ℂ) else 1).prod) =
      if configuration ∈ configurations then (-1 : ℂ) else 1 := by
  induction configurations with
  | nil => simp
  | cons other rest inductionHypothesis =>
      obtain ⟨notInRest, restNodup⟩ := List.nodup_cons.mp nodup
      by_cases same : other = configuration
      · subst other
        have tailProduct := signProduct_eq_one_of_not_mem placement branch
          configuration output configurationMatch rest notInRest
        simp only [List.map_cons, List.prod_cons]
        simp [configurationMatch, notInRest, tailProduct]
      · have firstFactor := signFactor_eq_one_of_ne placement branch
          configuration other output configurationMatch same
        have tailProduct := inductionHypothesis restNodup
        simp only [List.map_cons, List.prod_cons]
        rw [firstFactor, tailProduct]
        have reverse : configuration ≠ other := Ne.symm same
        simp [reverse]

def signRotationInstructionWhen
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p) :
    CleanRotationInstruction qubits placement.scratch where
  controls := (branch, true) :: configurationControlsAt placement configuration
  target := placement.phase
  angle := .mul (rationalAngle 2) .pi
  enoughScratch := configurationControlsAtWhen_enoughScratch placement branch
    facts configuration
  layoutNodup := configurationControlsAtWhen_layoutNodup placement branch
    facts configuration

/-- The actual sign stage is a diagonal product of one minus sign for every
negative configuration whose delimiter controls match the output basis.
The next semantic step is to prove uniqueness of that matching configuration.
-/
theorem SparseInitial.signAtWhen_applyOperator
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.support.filter fun configuration =>
              input.amplitude configuration < 0).map fun configuration =>
                Circuit.boolMultiControlledRy
                  ((branch, true) :: configurationControlsAt placement
                    configuration)
                  placement.scratch placement.phase
                  (.mul (rationalAngle 2) .pi)))
        state output =
      (((input.support.filter fun configuration =>
          input.amplitude configuration < 0).map fun configuration =>
            if boolControlsSatisfied
                ((branch, true) :: configurationControlsAt placement
                  configuration) output then (-1 : ℂ) else 1).prod) *
        state output := by
  let instructions : List (CleanRotationInstruction qubits placement.scratch) :=
    (input.support.filter fun configuration =>
      input.amplitude configuration < 0).map fun configuration =>
        signRotationInstructionWhen placement branch facts configuration
  have signAngles : ∀ instruction ∈ instructions,
      instruction.angle = .mul (rationalAngle 2) .pi := by
    intro instruction member
    dsimp [instructions] at member
    rcases List.mem_map.mp member with ⟨configuration, _, rfl⟩
    rfl
  simpa only [instructions, List.map_map, Function.comp_def,
    CleanRotationInstruction.compile, signRotationInstructionWhen] using
    compiledSignRotations_applyOperator placement.scratch instructions
      signAngles state supportScratch output

/-- On a represented legal configuration, the actual sign stage applies
exactly the sign prescribed by the sparse initial amplitude. This is used
only after the theoretical amplitude function is put into the shared input.
-/
theorem SparseInitial.signAtWhen_on_configuration
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p)
    (configurationInSupport : configuration ∈ input.support)
    (supportNodup : input.support.Nodup)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (configurationMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.support.filter fun candidate =>
              input.amplitude candidate < 0).map fun candidate =>
                Circuit.boolMultiControlledRy
                  ((branch, true) :: configurationControlsAt placement candidate)
                  placement.scratch placement.phase
                  (.mul (rationalAngle 2) .pi)))
        state output =
      (if input.amplitude configuration < 0 then (-1 : ℂ) else 1) *
        state output := by
  rw [SparseInitial.signAtWhen_applyOperator input placement branch facts state
    supportScratch output]
  have negativeNodup :
      (input.support.filter fun candidate => input.amplitude candidate < 0).Nodup :=
    supportNodup.filter _
  rw [signProduct_eq_if_mem placement branch configuration output
    configurationMatch _ negativeNodup]
  simp [configurationInSupport]

/-- The theoretical rational-amplitude adapter discharges support coverage
and deduplication internally, so no numerical-input correctness assumption
appears in the eventual `bPlus` proof. -/
theorem SparseInitial.ofAmplitude_signAtWhen_on_configuration
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (configurationMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true) :
    let input := SparseInitial.ofAmplitude amplitude
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.support.filter fun candidate =>
              input.amplitude candidate < 0).map fun candidate =>
                Circuit.boolMultiControlledRy
                  ((branch, true) :: configurationControlsAt placement candidate)
                  placement.scratch placement.phase
                  (.mul (rationalAngle 2) .pi)))
        state output =
      (if amplitude configuration < 0 then (-1 : ℂ) else 1) *
        state output := by
  let input := SparseInitial.ofAmplitude amplitude
  have supportNodup : input.support.Nodup := by
    rw [show input.support = (Finset.univ.toList : List (QConfiguration p))
      from SparseInitial.support_ofAmplitude amplitude]
    exact Finset.nodup_toList Finset.univ
  have configurationInSupport : configuration ∈ input.support := by
    rw [show input.support = (Finset.univ.toList : List (QConfiguration p))
      from SparseInitial.support_ofAmplitude amplitude]
    simp
  simpa only [input, SparseInitial.amplitude_ofAmplitude] using
    SparseInitial.signAtWhen_on_configuration input placement branch facts
      configuration configurationInSupport supportNodup state supportScratch
      output configurationMatch

theorem SparseInitial.signAtWhen_false_branch_output
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.sequence <|
            (input.support.filter fun configuration =>
              input.amplitude configuration < 0).map fun configuration =>
                Circuit.boolMultiControlledRy
                  ((branch, true) :: configurationControlsAt placement
                    configuration)
                  placement.scratch placement.phase
                  (.mul (rationalAngle 2) .pi)))
        state output = state output := by
  let instructions : List (CleanRotationInstruction qubits placement.scratch) :=
    (input.support.filter fun configuration =>
      input.amplitude configuration < 0).map fun configuration =>
        signRotationInstructionWhen placement branch facts configuration
  have branchControlled : ∀ instruction ∈ instructions,
      ∃ controls, instruction.controls = (branch, true) :: controls := by
    intro instruction member
    dsimp [instructions] at member
    rcases List.mem_map.mp member with ⟨configuration, _, rfl⟩
    exact ⟨configurationControlsAt placement configuration, rfl⟩
  simpa only [instructions, List.map_map, Function.comp_def,
    CleanRotationInstruction.compile, signRotationInstructionWhen] using
    compiledCleanRotations_false_branch_output placement.scratch branch
      instructions branchControlled state supportScratch output branchFalse

/-- Even in a superposition of both branches, the extension-branch
amplitudes are unchanged by the conditional configuration preparation. -/
theorem SparseInitial.circuitAtWhen_false_branch_output
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.circuitAtWhen placement branch)) state output = state output := by
  unfold SparseInitial.circuitAtWhen
  simp only [Circuit.denote_seq, applyOperator_mul]
  rw [SparseInitial.signAtWhen_false_branch_output input placement branch
    facts _
    (SparseInitial.magnitudeAtWhen_preserves_scratchZero input placement
      branch facts.toBranchPlacementFacts state supportScratch) output
    branchFalse]
  exact SparseInitial.magnitudeAtWhen_false_branch_output input placement
    branch facts.toBranchPlacementFacts state supportScratch output branchFalse

/-- For the approved theoretical amplitude function, all that remains after
this theorem is the magnitude-tree state equation: the sign stage already
matches the independent initial vector at every encoded configuration. -/
theorem SparseInitial.ofAmplitude_circuitAtWhen_on_configuration
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits)
    (configurationMatch : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude amplitude).circuitAtWhen placement branch))
        state output =
      (if amplitude configuration < 0 then (-1 : ℂ) else 1) *
        applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (Circuit.sequence <|
              (List.finRange p.systemWidth).map fun depth =>
                Circuit.sequence <|
                  ((SparseInitial.ofAmplitude amplitude).activePatterns
                    depth.val).map fun pattern =>
                    Circuit.boolMultiControlledRy
                      ((branch, true) :: prefixControlsAt placement depth pattern)
                      placement.scratch (placement.data depth)
                      ((SparseInitial.ofAmplitude amplitude).branchAngle
                        depth.val pattern)))
          state output := by
  unfold SparseInitial.circuitAtWhen
  simp only [Circuit.denote_seq, applyOperator_mul]
  exact SparseInitial.ofAmplitude_signAtWhen_on_configuration amplitude
    placement branch facts configuration _
    (SparseInitial.magnitudeAtWhen_preserves_scratchZero
      (SparseInitial.ofAmplitude amplitude) placement branch
      facts.toBranchPlacementFacts state supportScratch)
    output configurationMatch

theorem hadamard_preserves_scratchZero
    {qubits : Nat} (scratches : List (Fin qubits)) (branch : Fin qubits)
    (branchOutside : branch ∉ scratches)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (support : SupportedOnScratchZero scratches state) :
    SupportedOnScratchZero scratches
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (.gate (.h branch))) state) := by
  intro output dirty
  change applyOperator (embedSingleQubitOperator branch localH) state output = 0
  rw [applyOperator_embedSingleQubitOperator_state]
  apply Finset.sum_eq_zero
  intro inputBit _
  obtain ⟨wire, member, wireTrue⟩ := dirty
  have wireNe : branch ≠ wire := by
    intro equal
    subst wire
    exact branchOutside member
  have dirtyAfterReplace :
      ∃ scratch ∈ scratches,
        replaceQubitWire output branch inputBit scratch = true := by
    refine ⟨wire, member, ?_⟩
    rw [replaceQubitWire_outside]
    · exact wireTrue
    · exact wireNe.symm
  rw [support _ dirtyAfterReplace]
  simp

theorem hadamard_zeroKet_false_branch_output
    {qubits : Nat} (branch : Fin qubits)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (.gate (.h branch)))
        (basisKet (fun _ => false : QubitBasis qubits)) output =
      (((1 / Real.sqrt 2 : ℝ) : ℂ) *
        basisKet (fun _ => false : QubitBasis qubits) output) := by
  have replaceFalse : replaceQubitWire output branch false = output := by
    simpa [branchFalse] using replaceQubitWire_self output branch
  have replaceTrue :
      replaceQubitWire output branch true ≠
        (fun _ => false : QubitBasis qubits) := by
    intro equal
    have atBranch := congrFun equal branch
    simp at atBranch
  change applyOperator (embedSingleQubitOperator branch localH)
    (basisKet (fun _ => false : QubitBasis qubits)) output = _
  rw [applyOperator_embedSingleQubitOperator_state]
  simp [localH, basisKet_apply, replaceFalse,
    replaceTrue, branchFalse]

theorem hadamard_zeroKet_true_branch_output
    {qubits : Nat} (branch : Fin qubits)
    (output : QubitBasis qubits) (branchTrue : output branch = true) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (.gate (.h branch)))
        (basisKet (fun _ => false : QubitBasis qubits)) output =
      (((1 / Real.sqrt 2 : ℝ) : ℂ) *
        basisKet
          (replaceQubitWire (fun _ => false : QubitBasis qubits)
            branch true) output) := by
  let oneBranch := replaceQubitWire
    (fun _ => false : QubitBasis qubits) branch true
  have replaceTrueNeZero : replaceQubitWire output branch true ≠
      (fun _ => false : QubitBasis qubits) := by
    intro equal
    have atBranch := congrFun equal branch
    simp at atBranch
  change applyOperator (embedSingleQubitOperator branch localH)
    (basisKet (fun _ => false : QubitBasis qubits)) output = _
  rw [applyOperator_embedSingleQubitOperator_state]
  by_cases equal : output = oneBranch
  · subst output
    have replaceFalseZero :
        replaceQubitWire oneBranch branch false =
          (fun _ => false : QubitBasis qubits) := by
      funext wire
      simp [oneBranch, replaceQubitWire]
    simp [localH, basisKet_apply, oneBranch, replaceFalseZero,
      replaceTrueNeZero]
  · have replaceFalseNeZero :
        replaceQubitWire output branch false ≠
          (fun _ => false : QubitBasis qubits) := by
      intro replaceZero
      apply equal
      funext wire
      by_cases atBranch : wire = branch
      · subst wire
        simp [oneBranch, branchTrue]
      · have atWire := congrFun replaceZero wire
        simp only [replaceQubitWire_outside _ _ _ _ atBranch] at atWire
        simp [oneBranch, replaceQubitWire, atBranch, atWire]
    simp [localH, basisKet_apply, oneBranch, equal,
      replaceFalseNeZero, replaceTrueNeZero, branchTrue]

theorem hadamard_zeroKet_superposition
    {qubits : Nat} (branch : Fin qubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (.gate (.h branch)))
        (basisKet (fun _ => false : QubitBasis qubits)) =
      fun output =>
        (((1 / Real.sqrt 2 : ℝ) : ℂ) *
          basisKet (fun _ => false : QubitBasis qubits) output) +
        (((1 / Real.sqrt 2 : ℝ) : ℂ) *
          basisKet
            (replaceQubitWire (fun _ => false : QubitBasis qubits)
              branch true) output) := by
  funext output
  by_cases branchTrue : output branch = true
  · have notZero : output ≠ (fun _ => false : QubitBasis qubits) := by
      intro equal
      have atBranch := congrFun equal branch
      simp [branchTrue] at atBranch
    rw [hadamard_zeroKet_true_branch_output branch output branchTrue]
    simp [basisKet_apply, notZero]
  · have branchFalse : output branch = false := by
      cases value : output branch <;> simp_all
    have notOne : output ≠
        replaceQubitWire (fun _ => false : QubitBasis qubits)
          branch true := by
      intro equal
      have atBranch := congrFun equal branch
      simp [branchFalse] at atBranch
    rw [hadamard_zeroKet_false_branch_output branch output branchFalse]
    simp [basisKet_apply, notOne]

/-- The history-branch amplitudes of Hadamard followed by the full magnitude
tree are the expected square-root masses, with the initial `1/√2` factor. -/
theorem SparseInitial.magnitudeAfterHadamard_canonical_amplitude
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : BranchPlacementFacts placement branch)
    (rootPos : 0 < input.branchMass 0 0)
    (pattern : Nat) (patternBound : pattern < 2 ^ p.systemWidth) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (SparseInitial.magnitudePrefixAtWhen input placement branch
            p.systemWidth))
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (.gate (.h branch)))
          (basisKet (fun _ => false : QubitBasis qubits)))
        (SparseInitial.prefixBasis placement branch facts p.systemWidth
          pattern) =
      (((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (Real.sqrt
          (((input.branchMass p.systemWidth pattern : ℚ) : ℝ) /
            ((input.branchMass 0 0 : ℚ) : ℝ)) : ℂ)) := by
  let scale : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  let zeroState : VerifiedCircuitCore.State (QubitBasis qubits) :=
    basisKet (fun _ => false : QubitBasis qubits)
  let oneState : VerifiedCircuitCore.State (QubitBasis qubits) :=
    basisKet (SparseInitial.prefixBasis placement branch facts 0 0)
  let magnitude := Circuit.denote
    (primitiveGateOperatorWithSymbols (fun _ => 0))
    (SparseInitial.magnitudePrefixAtWhen input placement branch p.systemWidth)
  let output := SparseInitial.prefixBasis placement branch facts
    p.systemWidth pattern
  have superposition :
      applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (.gate (.h branch))) zeroState =
        scale • zeroState + scale • oneState := by
    funext basis
    have h := congrFun (hadamard_zeroKet_superposition branch) basis
    simpa only [scale, zeroState, oneState, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul,
      SparseInitial.prefixBasis_zero_eq_branch_one] using h
  have zeroOutput : zeroState output = 0 := by
    have branchTrue := SparseInitial.prefixBasis_branch placement branch facts
      p.systemWidth pattern
    have different : output ≠ (fun _ => false : QubitBasis qubits) := by
      intro equal
      have atBranch := congrFun equal branch
      simp [output, branchTrue] at atBranch
    simp [zeroState, basisKet_apply, different]
  have oneAmplitude : applyOperator magnitude oneState output =
      (Real.sqrt
        (((input.branchMass p.systemWidth pattern : ℚ) : ℝ) /
          ((input.branchMass 0 0 : ℚ) : ℝ)) : ℂ) := by
    exact SparseInitial.magnitudePrefixAtWhen_basisKet_amplitude input
      placement branch facts rootPos p.systemWidth le_rfl pattern patternBound
  have zeroIdentity : applyOperator magnitude zeroState = zeroState :=
    SparseInitial.magnitudePrefixAtWhen_zeroKet_identity input placement branch
      facts
  change applyOperator magnitude
    (applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (.gate (.h branch))) zeroState) output = _
  rw [superposition, applyOperator_add, applyOperator_smul,
    applyOperator_smul, zeroIdentity]
  simp [Pi.add_apply, Pi.smul_apply, zeroOutput, oneAmplitude, scale]

/-- At an encoded configuration, the shared conditional preparer has the
theoretical Hadamard weight, square-root mass, and exact sign factor. -/
theorem SparseInitial.ofAmplitude_circuitAfterHadamard_on_configuration
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0)
    (configuration : QConfiguration p) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude amplitude).circuitAtWhen placement branch))
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (.gate (.h branch)))
          (basisKet (fun _ => false : QubitBasis qubits)))
        (SparseInitial.prefixBasis placement branch
          facts.toBranchPlacementFacts p.systemWidth
          (prefixPattern configuration p.systemWidth)) =
      (if amplitude configuration < 0 then (-1 : ℂ) else 1) *
        (((1 / Real.sqrt 2 : ℝ) : ℂ) *
          (Real.sqrt
            ((((SparseInitial.ofAmplitude amplitude).branchMass p.systemWidth
                (prefixPattern configuration p.systemWidth) : ℚ) : ℝ) /
              (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ)) :
              ℂ)) := by
  let input := SparseInitial.ofAmplitude amplitude
  let zeroState : VerifiedCircuitCore.State (QubitBasis qubits) :=
    basisKet (fun _ => false : QubitBasis qubits)
  let hadamard := Circuit.denote
    (primitiveGateOperatorWithSymbols (fun _ => 0)) (.gate (.h branch))
  let output := SparseInitial.prefixBasis placement branch
    facts.toBranchPlacementFacts p.systemWidth
    (prefixPattern configuration p.systemWidth)
  have zeroScratch : SupportedOnScratchZero placement.scratch zeroState := by
    intro basis dirty
    obtain ⟨wire, _, trueAt⟩ := dirty
    have different : basis ≠ (fun _ => false : QubitBasis qubits) := by
      intro equal
      have atWire := congrFun equal wire
      simp [trueAt] at atWire
    simp [zeroState, basisKet_apply, different]
  have hadamardScratch : SupportedOnScratchZero placement.scratch
      (applyOperator hadamard zeroState) :=
    hadamard_preserves_scratchZero placement.scratch branch
      facts.branchOutsideScratch zeroState zeroScratch
  have controls : boolControlsSatisfied
      ((branch, true) :: configurationControlsAt placement configuration)
      output = true :=
    SparseInitial.prefixBasis_configuration_controls placement branch
      facts.toBranchPlacementFacts configuration
  have signEq := SparseInitial.ofAmplitude_circuitAtWhen_on_configuration
    amplitude placement branch facts configuration
    (applyOperator hadamard zeroState) hadamardScratch output controls
  have magnitudeEq :=
    SparseInitial.magnitudeAfterHadamard_canonical_amplitude input placement
      branch facts.toBranchPlacementFacts rootPos
      (prefixPattern configuration p.systemWidth)
      (prefixPattern_lt configuration p.systemWidth)
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (input.circuitAtWhen placement branch))
      (applyOperator hadamard zeroState) output = _
  calc
    _ = (if amplitude configuration < 0 then (-1 : ℂ) else 1) *
          applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (SparseInitial.magnitudePrefixAtWhen input placement branch
                p.systemWidth))
            (applyOperator hadamard zeroState) output := by
              simpa only [SparseInitial.magnitudePrefixAtWhen_full,
                SparseInitial.magnitudeLayerAtWhen] using signEq
    _ = _ := by rw [magnitudeEq]

/-- On each encoded scientific configuration, the theoretical sparse input
gives the normalized initial amplitude in the history branch.  This is a
component of the theoretical `bPlus` proof, not a claim about numerical QSP
output. -/
theorem SparseInitial.ofAmplitude_circuitAfterHadamard_normalized
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0)
    (configuration : QConfiguration p) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude amplitude).circuitAtWhen placement branch))
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (.gate (.h branch)))
          (basisKet (fun _ => false : QubitBasis qubits)))
        (SparseInitial.prefixBasis placement branch
          facts.toBranchPlacementFacts p.systemWidth
          (prefixPattern configuration p.systemWidth)) =
      (((1 / Real.sqrt 2 : ℝ) *
        ((amplitude configuration : ℝ) /
          Real.sqrt
            (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ))) : ℂ) := by
  rw [SparseInitial.ofAmplitude_circuitAfterHadamard_on_configuration
    amplitude placement branch facts rootPos configuration,
    SparseInitial.branchMass_leaf_ofAmplitude]
  have rootPosReal :
      0 < (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ) := by
    exact_mod_cast rootPos
  have signIdentity := signed_sqrt_square_over_positive
    (amplitude configuration : ℝ)
    (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ)
    rootPosReal
  have signTest :
      ((amplitude configuration : ℝ) < 0) ↔
        amplitude configuration < 0 := by norm_cast
  simp only [signTest] at signIdentity
  have scaled := congrArg (fun value : ℝ =>
    (1 / Real.sqrt 2 : ℝ) * value) signIdentity
  calc
    _ = (((1 / Real.sqrt 2 : ℝ) *
          ((if amplitude configuration < 0 then (-1 : ℝ) else 1) *
            Real.sqrt
              (((amplitude configuration : ℝ) ^ 2) /
                (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ)))) : ℂ) := by
          by_cases negative : amplitude configuration < 0
          · simp [negative]
          · simp [negative]
    _ = _ := by exact_mod_cast scaled

theorem SparseInitial.bPlusPreparation_zeroKet_normalized
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) :
    IsNormalizedState
      (applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.bPlusPreparation placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits))) := by
  have initial : IsNormalizedState
      (basisKet (fun _ => false : QubitBasis qubits)) := by
    simp [IsNormalizedState, basisProbability, basisKet]
  exact initial.applyOperator_of_mem_unitaryGroup
    (primitiveCircuit_denote_mem_unitaryGroup (fun _ => 0)
      (input.bPlusPreparation placement branch).circuit)

theorem SparseInitial.ofAmplitude_bPlusPreparation_on_configuration
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0)
    (configuration : QConfiguration p) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude amplitude).bPlusPreparation
            placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits))
        (SparseInitial.prefixBasis placement branch
          facts.toBranchPlacementFacts p.systemWidth
          (prefixPattern configuration p.systemWidth)) =
      (((1 / Real.sqrt 2 : ℝ) *
        ((amplitude configuration : ℝ) /
          Real.sqrt
            (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ))) : ℂ) := by
  rw [SparseInitial.bPlusPreparation_circuit, Circuit.denote_seq,
    applyOperator_mul]
  exact SparseInitial.ofAmplitude_circuitAfterHadamard_normalized
    amplitude placement branch facts rootPos configuration

/-- The extension (branch=false) amplitudes of the theoretical shared
preparer are exactly those produced by its initial Hadamard.  The history
branch still needs the tree-amplitude and sign proof before this can be
identified with the independent `bPlus` state. -/
theorem SparseInitial.bPlusPreparation_false_branch_output
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (state : VerifiedCircuitCore.State (QubitBasis qubits))
    (supportScratch : SupportedOnScratchZero placement.scratch state)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.bPlusPreparation placement branch).circuit) state output =
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (.gate (.h branch))) state output := by
  rw [SparseInitial.bPlusPreparation_circuit, Circuit.denote_seq,
    applyOperator_mul]
  exact SparseInitial.circuitAtWhen_false_branch_output input placement
    branch facts _
    (hadamard_preserves_scratchZero placement.scratch branch
      facts.branchOutsideScratch state supportScratch) output branchFalse

theorem SparseInitial.bPlusPreparation_zeroKet_false_branch_output
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (output : QubitBasis qubits) (branchFalse : output branch = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (input.bPlusPreparation placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits)) output =
      (((1 / Real.sqrt 2 : ℝ) : ℂ) *
        basisKet (fun _ => false : QubitBasis qubits) output) := by
  rw [SparseInitial.bPlusPreparation_false_branch_output input placement
    branch facts _ (by
      intro basis dirty
      simp only [basisKet_apply]
      have basisNe : basis ≠ (fun _ => false : QubitBasis qubits) := by
        intro equal
        rcases dirty with ⟨wire, _, wireTrue⟩
        have atWire := congrFun equal wire
        simp [wireTrue] at atWire
      simp [basisNe]) output branchFalse]
  exact hadamard_zeroKet_false_branch_output branch output branchFalse

/-- The specified extension basis and every encoded history configuration
already account for all unit probability mass of the theoretical shared
preparation.  No claim is made for externally supplied numerical phases. -/
theorem SparseInitial.ofAmplitude_bPlusPreparation_selected_mass
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0) :
    let output := applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        ((SparseInitial.ofAmplitude amplitude).bPlusPreparation
          placement branch).circuit)
      (basisKet (fun _ => false : QubitBasis qubits))
    Complex.normSq (output (fun _ => false)) +
      (∑ configuration : QConfiguration p,
        Complex.normSq
          (output (SparseInitial.prefixBasis placement branch
            facts.toBranchPlacementFacts p.systemWidth
            (prefixPattern configuration p.systemWidth)))) = 1 := by
  let output := applyOperator
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      ((SparseInitial.ofAmplitude amplitude).bPlusPreparation
        placement branch).circuit)
    (basisKet (fun _ => false : QubitBasis qubits))
  let root : ℝ :=
    (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ)
  have zeroAmplitude : output (fun _ => false : QubitBasis qubits) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    simp [output, basisKet_apply,
      SparseInitial.bPlusPreparation_zeroKet_false_branch_output
        (SparseInitial.ofAmplitude amplitude) placement branch facts
        (fun _ => false : QubitBasis qubits) (by simp)]
  have zeroMass : Complex.normSq
      (output (fun _ => false : QubitBasis qubits)) = 1 / 2 := by
    rw [zeroAmplitude]
    simpa only [mul_one, one_pow] using (half_branch_normSq 1)
  have configurationMass :
      (∑ configuration : QConfiguration p,
        Complex.normSq
          (output (SparseInitial.prefixBasis placement branch
            facts.toBranchPlacementFacts p.systemWidth
            (prefixPattern configuration p.systemWidth)))) =
      ∑ configuration : QConfiguration p,
        (((amplitude configuration : ℝ) / Real.sqrt root) ^ 2 / 2) := by
    apply Finset.sum_congr rfl
    intro configuration _
    rw [show output
      (SparseInitial.prefixBasis placement branch
        facts.toBranchPlacementFacts p.systemWidth
        (prefixPattern configuration p.systemWidth)) =
      (((1 / Real.sqrt 2 : ℝ) *
        ((amplitude configuration : ℝ) / Real.sqrt root)) : ℂ) by
      simpa [output, root] using
        (SparseInitial.ofAmplitude_bPlusPreparation_on_configuration
          amplitude placement branch facts rootPos configuration)]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div] using
      (half_branch_normSq
        ((amplitude configuration : ℝ) / Real.sqrt root))
  dsimp only
  rw [zeroMass, configurationMass, ← Finset.sum_div]
  have total := SparseInitial.ofAmplitude_normalized_real_mass amplitude rootPos
  change (∑ configuration : QConfiguration p,
    ((amplitude configuration : ℝ) / Real.sqrt root) ^ 2) = 1 at total
  rw [total]
  norm_num

/-- No amplitude leaks to any physical basis other than the extension basis
or an encoded history configuration.  This closes the support part of the
theoretical common preparation proof without certifying numerical output. -/
theorem SparseInitial.ofAmplitude_bPlusPreparation_zero_outside_catalog
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0)
    (basis : QubitBasis qubits)
    (outsideZero : basis ≠ (fun _ => false : QubitBasis qubits))
    (outsideConfiguration : ∀ configuration : QConfiguration p,
      basis ≠ SparseInitial.prefixBasis placement branch
        facts.toBranchPlacementFacts p.systemWidth
        (prefixPattern configuration p.systemWidth)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude amplitude).bPlusPreparation
            placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits)) basis = 0 := by
  let output := applyOperator
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      ((SparseInitial.ofAmplitude amplitude).bPlusPreparation
        placement branch).circuit)
    (basisKet (fun _ => false : QubitBasis qubits))
  let encode : QConfiguration p → QubitBasis qubits :=
    fun configuration => SparseInitial.prefixBasis placement branch
      facts.toBranchPlacementFacts p.systemWidth
      (prefixPattern configuration p.systemWidth)
  let selected : Finset (QubitBasis qubits) :=
    insert (fun _ => false) (Finset.univ.image encode)
  have injective : Function.Injective encode :=
    SparseInitial.configurationBasis_injective placement branch
      facts.toBranchPlacementFacts
  have zeroNotImage :
      (fun _ => false : QubitBasis qubits) ∉ Finset.univ.image encode := by
    intro member
    rcases Finset.mem_image.mp member with ⟨configuration, _, equal⟩
    exact SparseInitial.configurationBasis_ne_zero placement branch
      facts.toBranchPlacementFacts configuration equal
  have imageMass :
      (∑ physical ∈ Finset.univ.image encode,
        Complex.normSq (output physical)) =
      ∑ configuration : QConfiguration p,
        Complex.normSq (output (encode configuration)) := by
    rw [Finset.sum_image]
    intro left _ right _ equal
    exact injective equal
  have selectedMass :
      (∑ physical ∈ selected, Complex.normSq (output physical)) = 1 := by
    rw [show selected = insert (fun _ => false) (Finset.univ.image encode) by rfl,
      Finset.sum_insert zeroNotImage, imageMass]
    exact SparseInitial.ofAmplitude_bPlusPreparation_selected_mass
      amplitude placement branch facts rootPos
  have basisOutside : basis ∉ selected := by
    intro member
    rcases Finset.mem_insert.mp member with equal | imageMember
    · exact outsideZero equal
    · rcases Finset.mem_image.mp imageMember with
        ⟨configuration, _, equal⟩
      exact outsideConfiguration configuration equal.symm
  have normalized := SparseInitial.bPlusPreparation_zeroKet_normalized
    (SparseInitial.ofAmplitude amplitude) placement branch
  exact normalized_state_zero_outside_saturated output normalized
    selected selectedMass basis basisOutside

/-- Physical encoding of the approved normalized initial vector together
with the orthogonal extension basis.  The target is defined from the input
amplitudes and placement, without referring to the circuit denotation. -/
noncomputable def encodedBPlusTarget
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch) :
    VerifiedCircuitCore.State (QubitBasis qubits) :=
  fun basis =>
    if basis = (fun _ => false : QubitBasis qubits) then
      ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if hasConfiguration : ∃ configuration : QConfiguration p,
        basis = SparseInitial.prefixBasis placement branch
          facts.toBranchPlacementFacts p.systemWidth
          (prefixPattern configuration p.systemWidth) then
      (((1 / Real.sqrt 2 : ℝ) *
        ((amplitude (Classical.choose hasConfiguration) : ℝ) /
          Real.sqrt
            (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ))) : ℂ)
    else 0

/-- The common finite constructor, instantiated with the approved
theoretical initial vector, prepares the complete encoded `bPlus` state.
This theorem is not applied to arbitrary numerical-provider output. -/
theorem SparseInitial.ofAmplitude_bPlusPreparation_eq_encodedBPlusTarget
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          ((SparseInitial.ofAmplitude amplitude).bPlusPreparation
            placement branch).circuit)
        (basisKet (fun _ => false : QubitBasis qubits)) =
      encodedBPlusTarget amplitude placement branch facts := by
  funext basis
  by_cases zeroBasis : basis = (fun _ => false : QubitBasis qubits)
  · subst basis
    rw [encodedBPlusTarget, if_pos rfl]
    simpa [basisKet_apply] using
      (SparseInitial.bPlusPreparation_zeroKet_false_branch_output
        (SparseInitial.ofAmplitude amplitude) placement branch facts
        (fun _ => false : QubitBasis qubits) (by simp))
  · by_cases hasConfiguration : ∃ configuration : QConfiguration p,
        basis = SparseInitial.prefixBasis placement branch
          facts.toBranchPlacementFacts p.systemWidth
          (prefixPattern configuration p.systemWidth)
    · let configuration := Classical.choose hasConfiguration
      have basisEq : basis = SparseInitial.prefixBasis placement branch
          facts.toBranchPlacementFacts p.systemWidth
          (prefixPattern configuration p.systemWidth) :=
        Classical.choose_spec hasConfiguration
      rw [encodedBPlusTarget, if_neg zeroBasis,
        dif_pos hasConfiguration]
      conv_lhs => rw [basisEq]
      exact SparseInitial.ofAmplitude_bPlusPreparation_on_configuration
        amplitude placement branch facts rootPos configuration
    · rw [encodedBPlusTarget, if_neg zeroBasis,
        dif_neg hasConfiguration]
      exact SparseInitial.ofAmplitude_bPlusPreparation_zero_outside_catalog
        amplitude placement branch facts rootPos basis zeroBasis
        (fun configuration equal =>
          hasConfiguration ⟨configuration, equal⟩)

/-- Public, circuit-independent physical label for one configuration in the
history branch. The separate `encodedBPlusTarget` gives this label its
approved initial amplitude. -/
def encodedBPlusConfigurationBasis
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p) : QubitBasis qubits :=
  VerifiedCircuitCore.fixedOutsideBasisEmbedding
    ⟨placement.data, facts.dataInjective⟩
    (fun outside => if outside.1 = branch then true else false)
    (fun bit => delimiterEncoding configuration bit)

theorem encodedBPlusConfigurationBasis_eq_prefix
    {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (configuration : QConfiguration p) :
    encodedBPlusConfigurationBasis placement branch facts configuration =
      SparseInitial.prefixBasis placement branch
        facts.toBranchPlacementFacts p.systemWidth
        (prefixPattern configuration p.systemWidth) := by
  unfold encodedBPlusConfigurationBasis SparseInitial.prefixBasis
    SparseInitial.dataEmbedding
  congr 1
  funext bit
  simp [bit.isLt, prefixPattern_testBit, encodedBit]

theorem encodedBPlusTarget_on_extension
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch) :
    encodedBPlusTarget amplitude placement branch facts
        (fun _ => false : QubitBasis qubits) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [encodedBPlusTarget]

theorem encodedBPlusTarget_on_configuration
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (rootPos : 0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0)
    (configuration : QConfiguration p) :
    encodedBPlusTarget amplitude placement branch facts
        (encodedBPlusConfigurationBasis placement branch facts
          configuration) =
      (((1 / Real.sqrt 2 : ℝ) *
        ((amplitude configuration : ℝ) /
          Real.sqrt
            (((SparseInitial.ofAmplitude amplitude).branchMass 0 0 : ℚ) : ℝ))) : ℂ) := by
  rw [encodedBPlusConfigurationBasis_eq_prefix]
  rw [← SparseInitial.ofAmplitude_bPlusPreparation_eq_encodedBPlusTarget
    amplitude placement branch facts rootPos]
  exact SparseInitial.ofAmplitude_bPlusPreparation_on_configuration
    amplitude placement branch facts rootPos configuration

/-- The independent target has no amplitude away from the extension label
and the public configuration labels. This states support of the theoretical
target, not correctness of a numerical-provider circuit. -/
theorem encodedBPlusTarget_zero_outside_catalog
    {p : QParameters} {qubits : Nat}
    (amplitude : QConfiguration p → ℚ)
    (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) (facts : SignPlacementFacts placement branch)
    (basis : QubitBasis qubits)
    (notZero : basis ≠ (fun _ => false : QubitBasis qubits))
    (notConfiguration : ∀ configuration : QConfiguration p,
      basis ≠ encodedBPlusConfigurationBasis placement branch facts
        configuration) :
    encodedBPlusTarget amplitude placement branch facts basis = 0 := by
  have noPrefix : ¬ ∃ configuration : QConfiguration p,
      basis = SparseInitial.prefixBasis placement branch
        facts.toBranchPlacementFacts p.systemWidth
        (prefixPattern configuration p.systemWidth) := by
    rintro ⟨configuration, equal⟩
    exact notConfiguration configuration
      (by simpa only [encodedBPlusConfigurationBasis_eq_prefix] using equal)
  simp only [encodedBPlusTarget, if_neg notZero, dif_neg noPrefix]

end
end QLean.Circuits.FiniteRationalConfigurationPreparationCorrectness
