import QLean.Circuits.Foundation.ConstructionMultiControlledRotationCorrectness
import QLean.Circuits.Foundation.ReversibleLogic

/-!
# Bool制御多重Ryの疎な正しさ

0制御wireをXで反転し、正制御AND鎖を使い、同じX列で戻す回路を、独立なBool制御式へ接続する。
一般幅では計算基底置換だけを追跡し、行列要素を列挙しない。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 一wireをXOR反転する回路非依存な基底作用。 -/
def xBasisAction {qubits : Nat} (target : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire target true input

/-- Bool制御列のうち期待値が0であるwireだけを取り出す。 -/
def zeroControlWires {qubits : Nat}
    (controls : List (Fin qubits × Bool)) : List (Fin qubits) :=
  controls.filterMap fun control => if control.2 then none else some control.1

/-- 0制御wire抽出を先頭要素で一段展開する。 -/
@[simp] theorem zeroControlWires_cons {qubits : Nat}
    (control : Fin qubits × Bool) (rest : List (Fin qubits × Bool)) :
    zeroControlWires (control :: rest) =
      if control.2 then zeroControlWires rest
      else control.1 :: zeroControlWires rest := by
  rcases control with ⟨wire, expected⟩
  cases expected <;> rfl

/-- wire列を実行順にX反転した計算基底作用。 -/
def flipWiresBasisAction {qubits : Nat} (wires : List (Fin qubits))
    (input : QubitBasis qubits) : QubitBasis qubits :=
  wires.foldl (fun state wire => xBasisAction wire state) input

/-- 作用関数列のfoldとwire列を直接foldする定義は一致する。 -/
theorem foldl_xBasisAction_eq_flipWiresBasisAction {qubits : Nat}
    (wires : List (Fin qubits)) (input : QubitBasis qubits) :
    (wires.map xBasisAction).foldl (fun state action => action state) input =
      flipWiresBasisAction wires input := by
  induction wires generalizing input with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      rw [inductionHypothesis]
      rfl

/-- 0制御反転回路の直接基底作用。 -/
def invertZeroControlsBasisAction {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (input : QubitBasis qubits) : QubitBasis qubits :=
  flipWiresBasisAction (zeroControlWires controls) input

/-- 重複のないwire列を反転した後の各bitは、所属時だけ反転される。 -/
theorem flipWiresBasisAction_apply {qubits : Nat}
    (wires : List (Fin qubits)) (nodup : wires.Nodup)
    (input : QubitBasis qubits) (wire : Fin qubits) :
    flipWiresBasisAction wires input wire =
      if wire ∈ wires then !input wire else input wire := by
  induction wires generalizing input with
  | nil => simp [flipWiresBasisAction]
  | cons head tail inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [flipWiresBasisAction, List.foldl_cons]
      change flipWiresBasisAction tail (xBasisAction head input) wire = _
      rw [inductionHypothesis tailNodup]
      by_cases equal : wire = head
      · subst wire
        simp [headFresh, xBasisAction, xorWire]
      · simp [equal, xBasisAction, xorWire]

/-- 重複のないwire列の反転作用は自己逆である。 -/
theorem flipWiresBasisAction_involutive {qubits : Nat}
    (wires : List (Fin qubits)) (nodup : wires.Nodup) :
    Function.Involutive (flipWiresBasisAction wires) := by
  intro input
  funext wire
  rw [flipWiresBasisAction_apply wires nodup,
    flipWiresBasisAction_apply wires nodup]
  by_cases member : wire ∈ wires <;> simp [member]

/-- 0制御wire列は元のcontrol wire列の部分列である。 -/
theorem zeroControlWires_subset {qubits : Nat}
    (controls : List (Fin qubits × Bool)) :
    ∀ wire ∈ zeroControlWires controls, wire ∈ controls.map Prod.fst := by
  intro wire member
  simp only [zeroControlWires, List.mem_filterMap] at member
  rcases member with ⟨control, controlMember, selected⟩
  cases expected : control.2 <;> simp [expected] at selected
  subst wire
  exact List.mem_map.mpr ⟨control, controlMember, rfl⟩

/-- control wireが重複しなければ0制御wire列も重複しない。 -/
theorem zeroControlWires_nodup {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (nodup : (controls.map Prod.fst).Nodup) :
    (zeroControlWires controls).Nodup := by
  induction controls with
  | nil => simp [zeroControlWires]
  | cons control rest inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      cases expected : control.2
      · rw [zeroControlWires_cons, expected]
        simp only [Bool.false_eq_true, if_false]
        exact List.nodup_cons.mpr ⟨fun member =>
          headFresh (zeroControlWires_subset rest control.1 member),
          inductionHypothesis tailNodup⟩
      · rw [zeroControlWires_cons, expected]
        simp only [if_true]
        exact inductionHypothesis tailNodup

/-- control列中の指定要素は、期待値0のときちょうど0制御wire列に入る。 -/
theorem mem_zeroControlWires_iff_of_mem {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (nodup : (controls.map Prod.fst).Nodup)
    (control : Fin qubits × Bool) (member : control ∈ controls) :
    control.1 ∈ zeroControlWires controls ↔ control.2 = false := by
  induction controls with
  | nil => simp at member
  | cons head rest inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst control
        cases expected : head.2
        · rw [zeroControlWires_cons, expected]
          simp
        · have absent : head.1 ∉ zeroControlWires rest := by
            intro zeroMember
            exact headFresh (zeroControlWires_subset rest head.1 zeroMember)
          rw [zeroControlWires_cons, expected]
          simp only [if_true, Bool.true_eq_false, iff_false]
          exact absent
      · have different : control.1 ≠ head.1 := by
          intro equal
          apply headFresh
          exact List.mem_map.mpr ⟨control, member, equal⟩
        cases expected : head.2
        · rw [zeroControlWires_cons, expected]
          simp only [Bool.false_eq_true, if_false]
          simp only [List.mem_cons, different, false_or]
          exact inductionHypothesis tailNodup member
        · rw [zeroControlWires_cons, expected]
          simp only [if_true]
          exact inductionHypothesis tailNodup member

/-- 0制御反転作用は自己逆である。 -/
theorem invertZeroControlsBasisAction_involutive {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (nodup : (controls.map Prod.fst).Nodup) :
    Function.Involutive (invertZeroControlsBasisAction controls) :=
  flipWiresBasisAction_involutive (zeroControlWires controls)
    (zeroControlWires_nodup controls nodup)

/-- 0制御反転回路のdenotationは直接基底作用の決定的作用素である。 -/
theorem invertZeroControls_operator {qubits : Nat}
    (controls : List (Fin qubits × Bool)) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.invertZeroControls controls) =
      deterministicOperator (invertZeroControlsBasisAction controls) := by
  unfold Circuit.invertZeroControls
  rw [Circuit.denote_fromList_eq_operatorSequence]
  have xOperator (wire : Fin qubits) :
      primitiveGateOperatorWithSymbols (fun _ => 0) (.x wire) =
        deterministicOperator (xBasisAction wire) := by
    rw [primitiveXOperator_eq_deterministicOperator]
    rfl
  have gateList :
      (controls.filterMap fun control =>
          if control.2 then none else some (PrimitiveGate.x control.1)).map
          (primitiveGateOperatorWithSymbols (fun _ => 0)) =
        (zeroControlWires controls).map fun wire =>
          deterministicOperator (xBasisAction wire) := by
    induction controls with
    | nil => rfl
    | cons control rest inductionHypothesis =>
        cases expected : control.2 <;>
          simp [zeroControlWires, expected, inductionHypothesis,
            xOperator]
  rw [gateList]
  have mappedOperators :
      (zeroControlWires controls).map
          (fun wire => deterministicOperator (xBasisAction wire)) =
        ((zeroControlWires controls).map xBasisAction).map
          deterministicOperator := by
    simp only [List.map_map, Function.comp_def]
  rw [mappedOperators, operatorSequence_deterministicOperator]
  congr 1
  funext input
  exact foldl_xBasisAction_eq_flipWiresBasisAction _ _

/-- 0制御反転回路は自己逆な置換行列である。 -/
theorem invertZeroControls_operator_eq_permMatrix {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (nodup : (controls.map Prod.fst).Nodup) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.invertZeroControls controls) =
      (involutiveBasisEquiv (invertZeroControlsBasisAction controls)
        (invertZeroControlsBasisAction_involutive controls nodup)).permMatrix ℂ := by
  rw [invertZeroControls_operator]
  exact deterministicOperator_eq_permMatrix_of_involutive _ _

/-- control外wireは0制御反転で保存される。 -/
theorem invertZeroControlsBasisAction_outside {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (nodup : (controls.map Prod.fst).Nodup)
    (wire : Fin qubits) (outside : wire ∉ controls.map Prod.fst)
    (input : QubitBasis qubits) :
    invertZeroControlsBasisAction controls input wire = input wire := by
  unfold invertZeroControlsBasisAction
  rw [flipWiresBasisAction_apply _ (zeroControlWires_nodup controls nodup)]
  rw [if_neg]
  intro member
  exact outside (zeroControlWires_subset controls wire member)

/-- Bool制御条件の直接判定。 -/
def boolControlsSatisfied {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (input : QubitBasis qubits) : Bool :=
  controls.all fun control => decide (input control.1 = control.2)

/-- 0制御を反転すると、全正制御条件は元のBool制御条件に一致する。 -/
theorem allWiresTrue_invertZeroControls {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (nodup : (controls.map Prod.fst).Nodup)
    (input : QubitBasis qubits) :
    ReversibleCircuit.allWiresTrue (controls.map Prod.fst)
        (invertZeroControlsBasisAction controls input) =
      boolControlsSatisfied controls input := by
  unfold ReversibleCircuit.allWiresTrue ReversibleCircuit.readWires
    boolControlsSatisfied invertZeroControlsBasisAction
  simp only [List.map_map]
  have valuesEqual :
      controls.map (flipWiresBasisAction (zeroControlWires controls) input ∘
        Prod.fst) =
      controls.map (fun control => decide (input control.1 = control.2)) := by
    apply List.map_congr_left
    intro control member
    change flipWiresBasisAction (zeroControlWires controls) input control.1 = _
    rw [flipWiresBasisAction_apply _ (zeroControlWires_nodup controls nodup)]
    have characterization :=
      mem_zeroControlWires_iff_of_mem controls nodup control member
    by_cases expected : control.2 = false
    · have zeroMember := characterization.mpr expected
      cases input control.1 <;> simp [zeroMember, expected]
    · have notMember : control.1 ∉ zeroControlWires controls :=
        fun zeroMember => expected (characterization.mp zeroMember)
      have controlTrue : control.2 = true := Bool.eq_true_of_not_eq_false expected
      cases input control.1 <;> simp [notMember, controlTrue]
  rw [valuesEqual]
  simp only [List.all_map, Function.comp_def, id_eq]

/-- Bool制御列が成立したときだけRyとなる独立な疎行列要素。 -/
def boolControlledRyAmplitude {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (angle : ℝ) (output input : QubitBasis qubits) : ℂ :=
  if agreesExcept target output input then
    if boolControlsSatisfied controls input then
      localRy angle (output target) (input target)
    else if output target = input target then 1 else 0
  else 0

/-- Bool制御多重Ryの基本gate列はclean scratch上で独立な疎作用に一致する。 -/
theorem boolMultiControlledRy_apply_sparse {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (scratches : List (Fin qubits))
    (target : Fin qubits) (angle : AngleExpr)
    (output input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.boolMultiControlledRy controls scratches target angle)
        output input =
      boolControlledRyAmplitude controls target angle.uniformValue output input := by
  have controlNodup : (controls.map Prod.fst).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp layoutNodup).1).1
  have prefixNodup : (controls.map Prod.fst ++ scratches).Nodup :=
    (List.nodup_append.mp layoutNodup).1
  have targetOutside : target ∉ controls.map Prod.fst := by
    have separated := (List.nodup_append.mp layoutNodup).2.2
    intro member
    exact separated target (List.mem_append_left scratches member)
      target (List.mem_cons_self) rfl
  have scratchOutside : ∀ scratch ∈ scratches,
      scratch ∉ controls.map Prod.fst := by
    intro scratch scratchMember controlMember
    have separated := (List.nodup_append.mp prefixNodup).2.2
    exact separated scratch controlMember scratch scratchMember rfl
  let permutation := involutiveBasisEquiv
    (invertZeroControlsBasisAction controls)
    (invertZeroControlsBasisAction_involutive controls controlNodup)
  have involutive : permutation.symm = permutation := rfl
  have firstScratchZero : ∀ wire ∈ scratches,
      invertZeroControlsBasisAction controls input wire = false := by
    intro wire member
    rw [invertZeroControlsBasisAction_outside controls controlNodup wire
      (scratchOutside wire member) input]
    exact scratchZero wire member
  unfold Circuit.boolMultiControlledRy
  simp only [Circuit.denote_seq]
  rw [invertZeroControls_operator_eq_permMatrix controls controlNodup]
  change (permutation.permMatrix ℂ *
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.positiveMultiControlledRy (controls.map Prod.fst)
          scratches target angle) *
      permutation.permMatrix ℂ) output input = _
  rw [permMatrix_conjugate_operator_apply permutation involutive]
  rw [positiveMultiControlledRy_apply_sparse (controls.map Prod.fst)
    scratches target angle (permutation output) (permutation input)
    (by simpa using enoughScratch) layoutNodup firstScratchZero]
  unfold boolControlledRyAmplitude positiveControlledRyAmplitude
  change (if agreesExcept target
      (invertZeroControlsBasisAction controls output)
      (invertZeroControlsBasisAction controls input) then _ else _) = _
  have agreement : agreesExcept target
      (invertZeroControlsBasisAction controls output)
      (invertZeroControlsBasisAction controls input) ↔
      agreesExcept target output input := by
    constructor
    · intro transformed wire different
      have value := transformed wire different
      unfold invertZeroControlsBasisAction at value
      rw [flipWiresBasisAction_apply _
          (zeroControlWires_nodup controls controlNodup),
        flipWiresBasisAction_apply _
          (zeroControlWires_nodup controls controlNodup)] at value
      by_cases member : wire ∈ zeroControlWires controls
      · simpa [member] using value
      · simpa [member] using value
    · intro original wire different
      unfold invertZeroControlsBasisAction
      rw [flipWiresBasisAction_apply _
          (zeroControlWires_nodup controls controlNodup),
        flipWiresBasisAction_apply _
          (zeroControlWires_nodup controls controlNodup)]
      by_cases member : wire ∈ zeroControlWires controls
      · simpa [member] using original wire different
      · simpa [member] using original wire different
  have permutationApply (state : QubitBasis qubits) :
      permutation state = invertZeroControlsBasisAction controls state := rfl
  rw [permutationApply input, permutationApply output]
  by_cases originalAgreement : agreesExcept target output input
  · have transformedAgreement := agreement.mpr originalAgreement
    simp only [if_pos originalAgreement, if_pos transformedAgreement]
    rw [allWiresTrue_invertZeroControls controls controlNodup input]
    rw [invertZeroControlsBasisAction_outside controls controlNodup target
      targetOutside output]
    rw [invertZeroControlsBasisAction_outside controls controlNodup target
      targetOutside input]
  · have transformedDisagreement : ¬ agreesExcept target
        (invertZeroControlsBasisAction controls output)
        (invertZeroControlsBasisAction controls input) :=
      fun transformedAgreement => originalAgreement (agreement.mp transformedAgreement)
    simp only [if_neg originalAgreement, if_neg transformedDisagreement]

end

end VerifiedCircuitCore
