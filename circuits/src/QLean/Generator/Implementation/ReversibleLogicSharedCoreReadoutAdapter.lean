import QLean.Generator.Implementation.ReversibleArithmeticCorrectness
import QLean.Generator.Implementation.ReversibleLogicSharedCoreAdapter
import QLean.Generator.Implementation.OracleTotalProgramsCompiler

/-!
# Shared reversible-logic actions and Q register readout

This narrow adapter connects the pure, validated shared-core action transport
to the established Q `readWires` observation API. It adds no compiler proof.
-/

namespace ProbabilityGeneratorQProof

open ReversibleCircuit

/-- The frozen collision-safe, zip-truncating XOR-copy compiler executes the
independent pure raw-copy stage.  This is a compiler bridge, not a list
induction. -/
theorem runBasis_rawXorCopy_eq_reference
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    (ReversibleCircuit.xorCopy source target).runBasis
        reversibleGatePermutation input =
      (TotalReversibleStage.xorCopy source target).reference input := by
  rw [← TotalReversibleStage.compile_xorCopy]
  exact TotalReversibleStage.compiledStage_runBasis_eq_reference _ input

/-- The frozen raw-copy compiler preserves each wire outside its target list,
by the shared raw-copy locality theorem and the Q compiler bridge. -/
theorem runBasis_rawXorCopy_outside_target
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ target) :
    (ReversibleCircuit.xorCopy source target).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_rawXorCopy_eq_reference]
  exact TotalReversibleStage.xorCopy_reference_apply_outside_target
    source target input wire outside

/--
On a validated layout, the frozen XOR-copy compiler executes the shared pure
register action. The proof factors through the shared total-stage contract.
-/
theorem runBasis_validatedXorCopy_eq_basisAction
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    (ReversibleCircuit.xorCopy layout.source.wires
        layout.target.wires).runBasis reversibleGatePermutation input =
      layout.basisAction input := by
  rw [← TotalReversibleStage.compile_xorCopy]
  change VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
      (TotalReversibleStage.xorCopy layout.source.wires
        layout.target.wires).compile input =
    layout.basisAction input
  rw [TotalReversibleStage.compiledStage_runBasis_eq_reference]
  exact layout.xorCopyStage_reference_eq_basisAction input

/-- The validated target readout is the pointwise source-target XOR. -/
theorem readWires_validatedRegisterXorCopyBasisAction_target
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    readWires layout.target.wires (layout.basisAction input) =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires layout.source.wires input)
        (readWires layout.target.wires input) := by
  unfold readWires ValidatedQRegister.wires
  simp only [List.map_map]
  generalize List.finRange width = indices
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, List.zipWith_cons_cons, Function.comp_apply]
      rw [layout.basisAction_readTarget, inductionHypothesis]
      cases input (layout.source.wire index) <;>
        cases input (layout.target.wire index) <;> rfl

/-- Raw-list validated XOR-copy execution as the shared pure action. -/
theorem runBasis_validatedXorCopyLists_eq_basisAction
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target) :
    let layout := ValidatedRegisterXorCopyLayout.ofLists source target
      sourceNodup targetNodup sameLength sourceTargetDisjoint
    (ReversibleCircuit.xorCopy source target).runBasis
        reversibleGatePermutation input = layout.basisAction input := by
  let layout := ValidatedRegisterXorCopyLayout.ofLists source target
    sourceNodup targetNodup sameLength sourceTargetDisjoint
  simpa [layout] using runBasis_validatedXorCopy_eq_basisAction layout input

/-- Raw-list validated XOR-copy target readout. -/
theorem readWires_validatedXorCopyLists_target
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target) :
    readWires target
        ((ReversibleCircuit.xorCopy source target).runBasis
          reversibleGatePermutation input) =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires source input) (readWires target input) := by
  let layout := ValidatedRegisterXorCopyLayout.ofLists source target
    sourceNodup targetNodup sameLength sourceTargetDisjoint
  rw [show (ReversibleCircuit.xorCopy source target).runBasis
      reversibleGatePermutation input = layout.basisAction input by
    simpa [layout] using runBasis_validatedXorCopy_eq_basisAction layout input]
  simpa [layout] using
    readWires_validatedRegisterXorCopyBasisAction_target layout input

/-- Raw-list validated XOR-copy preserves one wire outside its target. -/
theorem runBasis_validatedXorCopyLists_outside
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (wire : Wire ancillaQubits systemQubits) (outsideTarget : wire ∉ target) :
    (ReversibleCircuit.xorCopy source target).runBasis
        reversibleGatePermutation input wire = input wire := by
  let layout := ValidatedRegisterXorCopyLayout.ofLists source target
    sourceNodup targetNodup sameLength sourceTargetDisjoint
  rw [show (ReversibleCircuit.xorCopy source target).runBasis
      reversibleGatePermutation input = layout.basisAction input by
    simpa [layout] using runBasis_validatedXorCopy_eq_basisAction layout input]
  apply layout.basisAction_applyOutside
  intro index equal
  apply outsideTarget
  change wire = target.get (Fin.cast sameLength index) at equal
  exact equal.symm ▸ List.get_mem target (Fin.cast sameLength index)

/--
On a validated layout, the frozen controlled-copy compiler executes the shared
pure controlled-register action. The proof uses the total-stage permutation
contract and the shared stage-reference theorem; it contains no gate-list
induction.
-/
theorem runBasis_validatedControlledXorCopy_eq_basisAction
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    (ProbabilityGeneratorQProof.controlledXorCopy layout.control
        layout.source.wires layout.target.wires).runBasis
        reversibleGatePermutation input =
      layout.basisAction input := by
  rw [← OracleTotalProgram.compile_controlledXorCopy]
  change VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
      (OracleTotalProgram.controlledXorCopy layout.control
        layout.source.wires layout.target.wires).compile input =
    layout.basisAction input
  rw [TotalReversibleStage.compiledStage_runBasis_eq_reference]
  exact layout.controlledXorCopyStage_reference_eq_basisAction input

/--
Reading the validated controlled-copy target after the shared pure action gives
the pointwise control-and-source XOR formula in Q wire order.
-/
theorem readWires_validatedControlledRegisterXorCopyBasisAction_target
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    readWires layout.target.wires (layout.basisAction input) =
      (List.finRange width).map fun index =>
        (input (layout.target.wire index) !=
          (input layout.control && input (layout.source.wire index))) := by
  unfold readWires ValidatedQRegister.wires
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  exact layout.basisAction_readTarget input index

/-- The validated target readout in the established list-level XOR form. -/
theorem readWires_validatedControlledRegisterXorCopyBasisAction_target_zipWith
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    readWires layout.target.wires (layout.basisAction input) =
      if input layout.control then
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (readWires layout.source.wires input)
          (readWires layout.target.wires input)
      else readWires layout.target.wires input := by
  rw [readWires_validatedControlledRegisterXorCopyBasisAction_target]
  by_cases enabled : input layout.control = true
  · simp [enabled, readWires, ValidatedQRegister.wires]
    intro index
    cases sourceValue : input (layout.source.wire index) <;>
      cases targetValue : input (layout.target.wire index) <;>
      rfl
  · have disabled : input layout.control = false :=
      Bool.eq_false_of_not_eq_true enabled
    simp [disabled, readWires, ValidatedQRegister.wires]

/-- A list disjoint from the validated target has unchanged Q readout. -/
theorem readWires_validatedControlledRegisterXorCopyBasisAction_outside
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits)
    (wires : List (Wire ancillaQubits systemQubits))
    (outsideTarget : ∀ wire ∈ wires, ∀ index,
      wire ≠ layout.target.wire index) :
    readWires wires (layout.basisAction input) = readWires wires input := by
  apply List.map_congr_left
  intro wire membership
  exact layout.basisAction_applyOutside input wire
    (outsideTarget wire membership)

/-- A raw-list validated controlled-copy execution theorem. -/
theorem runBasis_validatedControlledXorCopyLists_eq_basisAction
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
      source target sourceNodup targetNodup sameLength sourceTargetDisjoint
      controlAbsentSource controlAbsentTarget
    (controlledXorCopy control source target).runBasis
        reversibleGatePermutation input = layout.basisAction input := by
  let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
    source target sourceNodup targetNodup sameLength sourceTargetDisjoint
    controlAbsentSource controlAbsentTarget
  simpa [layout] using
    runBasis_validatedControlledXorCopy_eq_basisAction layout input

/-- Raw-list validated controlled-copy target readout. -/
theorem readWires_validatedControlledXorCopyLists_target
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    readWires target
        ((controlledXorCopy control source target).runBasis
          reversibleGatePermutation input) =
      if input control then
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (readWires source input) (readWires target input)
      else readWires target input := by
  let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
    source target sourceNodup targetNodup sameLength sourceTargetDisjoint
    controlAbsentSource controlAbsentTarget
  rw [show (controlledXorCopy control source target).runBasis
      reversibleGatePermutation input = layout.basisAction input by
    simpa [layout] using
      runBasis_validatedControlledXorCopy_eq_basisAction layout input]
  simpa [layout] using
    readWires_validatedControlledRegisterXorCopyBasisAction_target_zipWith
      layout input

/-- Raw-list validated controlled-copy preserves a list outside its target. -/
theorem readWires_validatedControlledXorCopyLists_outside
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target)
    (outsideTarget : wires.Disjoint target) :
    readWires wires
        ((controlledXorCopy control source target).runBasis
          reversibleGatePermutation input) = readWires wires input := by
  let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
    source target sourceNodup targetNodup sameLength sourceTargetDisjoint
    controlAbsentSource controlAbsentTarget
  rw [show (controlledXorCopy control source target).runBasis
      reversibleGatePermutation input = layout.basisAction input by
  simpa [layout] using
      runBasis_validatedControlledXorCopy_eq_basisAction layout input]
  apply readWires_validatedControlledRegisterXorCopyBasisAction_outside
  intro wire wireMember index equal
  apply (List.disjoint_left.mp outsideTarget wireMember)
  change wire = target.get (Fin.cast sameLength index) at equal
  exact equal.symm ▸ List.get_mem target (Fin.cast sameLength index)

/-- Raw-list validated controlled-copy preserves one wire outside its target. -/
theorem runBasis_validatedControlledXorCopyLists_outside
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target)
    (wire : Wire ancillaQubits systemQubits) (outsideTarget : wire ∉ target) :
    (controlledXorCopy control source target).runBasis
        reversibleGatePermutation input wire = input wire := by
  let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
    source target sourceNodup targetNodup sameLength sourceTargetDisjoint
    controlAbsentSource controlAbsentTarget
  rw [show (controlledXorCopy control source target).runBasis
      reversibleGatePermutation input = layout.basisAction input by
    simpa [layout] using
      runBasis_validatedControlledXorCopy_eq_basisAction layout input]
  apply layout.basisAction_applyOutside
  intro index equal
  apply outsideTarget
  change wire = target.get (Fin.cast sameLength index) at equal
  exact equal.symm ▸ List.get_mem target (Fin.cast sameLength index)

/-- A validated controlled copy is the identity when its control is false. -/
theorem runBasis_validatedControlledXorCopyLists_of_control_false
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target)
    (controlFalse : input control = false) :
    (controlledXorCopy control source target).runBasis
        reversibleGatePermutation input = input := by
  let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
    source target sourceNodup targetNodup sameLength sourceTargetDisjoint
    controlAbsentSource controlAbsentTarget
  rw [show (controlledXorCopy control source target).runBasis
      reversibleGatePermutation input = layout.basisAction input by
    simpa [layout] using
      runBasis_validatedControlledXorCopy_eq_basisAction layout input]
  funext wire
  by_cases targetMember : wire ∈ layout.target.wires
  · rw [ValidatedQRegister.wires] at targetMember
    rcases List.mem_map.mp targetMember with ⟨index, _, equal⟩
    subst wire
    rw [layout.basisAction_readTarget]
    simp [layout, controlFalse]
  · exact layout.basisAction_applyOutside input wire fun index equal =>
      targetMember (by
        rw [ValidatedQRegister.wires]
        apply List.mem_map.mpr
        exact ⟨index, List.mem_finRange index, equal.symm⟩)

end ProbabilityGeneratorQProof
