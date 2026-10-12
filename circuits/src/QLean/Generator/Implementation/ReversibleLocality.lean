import QLean.Generator.Implementation.ReversibleArithmetic

/-!
# 可逆基本ゲート回路の疎な局所性

回路が参照するwire集合上の値だけで作用が決まり、その外側を変更しないことを構文帰納法で
証明する。これにより巨大行列を作らず、compute--use--uncomputeのwork消去を一般化する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 一個の可逆基本ゲートが読み書きする全wire。 -/
def reversibleGateWires
    {ancillaQubits systemQubits : Nat} :
    ReversibleGate ancillaQubits systemQubits →
      List (Wire ancillaQubits systemQubits)
  | .x target => [target]
  | .cnot control target _ => [control, target]
  | .toffoli control₁ control₂ target _ _ _ => [control₁, control₂, target]

/-- 二つの計算基底が指定wire集合上で一致すること。 -/
def BasisAgreeOn
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (left right : JointBasis ancillaQubits systemQubits) : Prop :=
  ∀ wire ∈ support, left wire = right wire

/-- repeatを使わない回路の全基本ゲートが指定support内のwireだけを参照すること。 -/
def circuitUsesOnly
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) → Prop
  | .identity => True
  | .gate gate => ∀ wire ∈ reversibleGateWires gate, wire ∈ support
  | .seq first second =>
      circuitUsesOnly support first ∧ circuitUsesOnly support second
  | .repeat _ _ => False

/-- 一個の可逆基本ゲートは参照wire集合外を変更しない。 -/
theorem reversibleGatePermutation_outside
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits)
    (outside : wire ∉ reversibleGateWires gate) :
    reversibleGatePermutation gate input wire = input wire := by
  cases gate with
  | x target =>
      have targetDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [reversibleGateWires, equal]
      change xBasisAction target input wire = input wire
      simp [xBasisAction, targetDifferent]
  | cnot control target different =>
      have targetDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [reversibleGateWires, equal]
      change cnotBasisAction control target input wire = input wire
      simp [cnotBasisAction, targetDifferent]
  | toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      have targetDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [reversibleGateWires, equal]
      change toffoliBasisAction control₁ control₂ target input wire = input wire
      simp [toffoliBasisAction, targetDifferent]

/-- support上で一致する二基底へ一ゲートを作用させてもsupport上で一致する。 -/
theorem reversibleGatePermutation_congr_on
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits)
    (support : List (Wire ancillaQubits systemQubits))
    (left right : JointBasis ancillaQubits systemQubits)
    (gateInside : ∀ wire ∈ reversibleGateWires gate, wire ∈ support)
    (agree : BasisAgreeOn support left right) :
    BasisAgreeOn support (reversibleGatePermutation gate left)
      (reversibleGatePermutation gate right) := by
  intro wire wireMember
  cases gate with
  | x target =>
      have targetMember : target ∈ support := gateInside target (by simp [reversibleGateWires])
      simp only [reversibleGatePermutation, xBasisEquiv, Equiv.coe_fn_mk]
      by_cases isTarget : wire = target
      · subst wire
        simp [xBasisAction, agree target targetMember]
      · simp [xBasisAction, isTarget, agree wire wireMember]
  | cnot control target different =>
      have controlMember : control ∈ support :=
        gateInside control (by simp [reversibleGateWires])
      have targetMember : target ∈ support :=
        gateInside target (by simp [reversibleGateWires])
      simp only [reversibleGatePermutation, cnotBasisEquiv, Equiv.coe_fn_mk]
      by_cases isTarget : wire = target
      · subst wire
        simp [cnotBasisAction, agree control controlMember, agree target targetMember]
      · simp [cnotBasisAction, isTarget, agree wire wireMember]
  | toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      have firstMember : control₁ ∈ support :=
        gateInside control₁ (by simp [reversibleGateWires])
      have secondMember : control₂ ∈ support :=
        gateInside control₂ (by simp [reversibleGateWires])
      have targetMember : target ∈ support :=
        gateInside target (by simp [reversibleGateWires])
      simp only [reversibleGatePermutation, toffoliBasisEquiv, Equiv.coe_fn_mk]
      by_cases isTarget : wire = target
      · subst wire
        simp [toffoliBasisAction, agree control₁ firstMember,
          agree control₂ secondMember, agree target targetMember]
      · simp [toffoliBasisAction, isTarget, agree wire wireMember]

/-- support内だけを使う回路はsupport外のwireを変更しない。 -/
theorem Circuit.runBasis_outside_of_usesOnly
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ circuit : Circuit (ReversibleGate ancillaQubits systemQubits),
      circuitUsesOnly support circuit →
      ∀ input wire, wire ∉ support →
        circuit.runBasis reversibleGatePermutation input wire = input wire
  | .identity, _, _, _, _ => rfl
  | .gate gate, usesOnly, input, wire, outside => by
      exact reversibleGatePermutation_outside gate input wire (by
        intro member
        exact outside (usesOnly wire member))
  | .seq first second, usesOnly, input, wire, outside => by
      calc
        (Circuit.seq first second).runBasis reversibleGatePermutation input wire =
            second.runBasis reversibleGatePermutation
              (first.runBasis reversibleGatePermutation input) wire := rfl
        _ = first.runBasis reversibleGatePermutation input wire :=
          Circuit.runBasis_outside_of_usesOnly support second usesOnly.2
            (first.runBasis reversibleGatePermutation input) wire outside
        _ = input wire :=
          Circuit.runBasis_outside_of_usesOnly support first usesOnly.1 input wire outside
  | .repeat count body, usesOnly, input, wire, outside => usesOnly.elim

/-- support上で一致する二基底へsupport内回路を作用させてもsupport上で一致する。 -/
theorem Circuit.runBasis_congr_on_of_usesOnly
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ circuit : Circuit (ReversibleGate ancillaQubits systemQubits),
      circuitUsesOnly support circuit →
      ∀ left right, BasisAgreeOn support left right →
        BasisAgreeOn support
          (circuit.runBasis reversibleGatePermutation left)
          (circuit.runBasis reversibleGatePermutation right)
  | .identity, _, left, right, agree => agree
  | .gate gate, usesOnly, left, right, agree =>
      reversibleGatePermutation_congr_on gate support left right usesOnly agree
  | .seq first second, usesOnly, left, right, agree => by
      change BasisAgreeOn support
        (second.runBasis reversibleGatePermutation
          (first.runBasis reversibleGatePermutation left))
        (second.runBasis reversibleGatePermutation
          (first.runBasis reversibleGatePermutation right))
      apply Circuit.runBasis_congr_on_of_usesOnly support second usesOnly.2
      exact Circuit.runBasis_congr_on_of_usesOnly support first usesOnly.1 left right agree
  | .repeat count body, usesOnly, left, right, agree => usesOnly.elim

/-- support内を入力へ戻し、support外だけuse後の値を残す基底。 -/
def restoreSupport
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (input used : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  fun wire => if wire ∈ support then input wire else used wire

/-- restoreSupportはsupport上で元入力に一致する。 -/
theorem restoreSupport_agrees_input
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (input used : JointBasis ancillaQubits systemQubits) :
    BasisAgreeOn support (restoreSupport support input used) input := by
  intro wire member
  simp [restoreSupport, member]

/-- restoreSupportはsupport外でuse後の状態に一致する。 -/
theorem restoreSupport_outside
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (input used : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ support) :
    restoreSupport support input used wire = used wire := by
  simp [restoreSupport, outside]

/--
computeがsupport内だけを使い、useがcompute後のsupport値を保存するなら、
compute--use--uncomputeはsupportを入力へ戻し、外部のuse結果だけを残す。
-/
theorem Circuit.computeUseUncompute_local_clean
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (compute use : Circuit (ReversibleGate ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (computeUsesOnly : circuitUsesOnly support compute)
    (usePreservesSupport :
      BasisAgreeOn support
        (use.runBasis reversibleGatePermutation
          (compute.runBasis reversibleGatePermutation input))
        (compute.runBasis reversibleGatePermutation input)) :
    (Circuit.computeUseUncompute id compute use).runBasis
        reversibleGatePermutation input =
      restoreSupport support input
        (use.runBasis reversibleGatePermutation
          (compute.runBasis reversibleGatePermutation input)) := by
  let computed := compute.runBasis reversibleGatePermutation input
  let used := use.runBasis reversibleGatePermutation computed
  let output := restoreSupport support input used
  have computeOutputOnSupport :
      BasisAgreeOn support (compute.runBasis reversibleGatePermutation output) computed := by
    exact Circuit.runBasis_congr_on_of_usesOnly support compute computeUsesOnly
      output input (restoreSupport_agrees_input support input used)
  have computeOutputEqualsUsed :
      compute.runBasis reversibleGatePermutation output = used := by
    funext wire
    by_cases inside : wire ∈ support
    · exact (computeOutputOnSupport wire inside).trans
        (usePreservesSupport wire inside).symm
    · rw [Circuit.runBasis_outside_of_usesOnly support compute computeUsesOnly
        output wire inside]
      exact restoreSupport_outside support input used wire inside
  exact Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute use input output
      computeOutputEqualsUsed.symm

/-- support包含関係に沿って`circuitUsesOnly`を拡張できる。 -/
theorem circuitUsesOnly_mono
    {ancillaQubits systemQubits : Nat}
    {small large : List (Wire ancillaQubits systemQubits)}
    (included : ∀ wire ∈ small, wire ∈ large) :
    ∀ circuit : Circuit (ReversibleGate ancillaQubits systemQubits),
      circuitUsesOnly small circuit → circuitUsesOnly large circuit
  | .identity, _ => trivial
  | .gate gate, usesOnly => by
      intro wire member
      exact included wire (usesOnly wire member)
  | .seq first second, usesOnly =>
      ⟨circuitUsesOnly_mono included first usesOnly.1,
        circuitUsesOnly_mono included second usesOnly.2⟩
  | .repeat count body, usesOnly => usesOnly.elim

/-- 両wireがsupport内ならsafe CNOTもsupport内だけを使う。 -/
theorem circuitUsesOnly_safeCnot
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (control target : Wire ancillaQubits systemQubits)
    (controlMember : control ∈ support) (targetMember : target ∈ support) :
    circuitUsesOnly support (safeCnot control target) := by
  unfold safeCnot
  split
  · intro wire member
    simp [reversibleGateWires] at member
    rcases member with rfl | rfl
    · exact controlMember
    · exact targetMember
  · trivial

/-- 三wireがsupport内ならsafe Toffoliもsupport内だけを使う。 -/
theorem circuitUsesOnly_safeToffoli
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (firstMember : control₁ ∈ support) (secondMember : control₂ ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (safeToffoli control₁ control₂ target) := by
  unfold safeToffoli
  split
  · split
    · split
      · intro wire member
        simp [reversibleGateWires] at member
        rcases member with rfl | rfl | rfl
        · exact firstMember
        · exact secondMember
        · exact targetMember
      · trivial
    · trivial
  · trivial

/-- support内回路の構文的逆も同じsupport内だけを使う。 -/
theorem circuitUsesOnly_reverse_id
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ circuit : Circuit (ReversibleGate ancillaQubits systemQubits),
      circuitUsesOnly support circuit → circuitUsesOnly support (circuit.reverse id)
  | .identity, _ => trivial
  | .gate _gate, usesOnly => usesOnly
  | .seq first second, usesOnly =>
      ⟨circuitUsesOnly_reverse_id support second usesOnly.2,
        circuitUsesOnly_reverse_id support first usesOnly.1⟩
  | .repeat _count _body, usesOnly => usesOnly.elim

/-- 各要素がsupport内だけを使う回路列なら、その逐次合成も同じsupport内だけを使う。 -/
theorem circuitUsesOnly_sequence
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ circuits : List (Circuit (ReversibleGate ancillaQubits systemQubits)),
      (∀ circuit ∈ circuits, circuitUsesOnly support circuit) →
      circuitUsesOnly support (Circuit.sequence circuits)
  | [], _ => trivial
  | circuit :: circuits, allUse => by
      constructor
      · exact allUse circuit (by simp)
      · apply circuitUsesOnly_sequence support circuits
        intro tailCircuit member
        exact allUse tailCircuit (by simp [member])

/-- targetがsupport内なら一量子ビットX回路もsupport内だけを使う。 -/
theorem circuitUsesOnly_x
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (targetMember : target ∈ support) :
    circuitUsesOnly support
      (.gate (.x target) : Circuit (ReversibleGate ancillaQubits systemQubits)) := by
  intro wire member
  simp only [reversibleGateWires, List.mem_singleton] at member
  subst wire
  exact targetMember

/-- 各ゲートの参照wireがsupport内なら、そのゲートリスト回路もsupport内だけを使う。 -/
theorem circuitUsesOnly_fromList
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ gates : List (ReversibleGate ancillaQubits systemQubits),
      (∀ gate ∈ gates, ∀ wire ∈ reversibleGateWires gate, wire ∈ support) →
      circuitUsesOnly support (Circuit.fromList gates)
  | [], _ => trivial
  | gate :: gates, allInside => by
      constructor
      · exact allInside gate (by simp)
      · apply circuitUsesOnly_fromList support gates
        intro tailGate gateMember wire wireMember
        exact allInside tailGate (by simp [gateMember]) wire wireMember

/-- Bool制御反転回路は制御wireを含むsupport内だけを使う。 -/
theorem circuitUsesOnly_invertZeroControls
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (controlsMember : ∀ control ∈ controls, control.1 ∈ support) :
    circuitUsesOnly support (invertZeroControls controls) := by
  apply circuitUsesOnly_fromList support
  intro gate gateMember wire wireMember
  rw [List.mem_filterMap] at gateMember
  rcases gateMember with ⟨control, controlMember, selected⟩
  split at selected
  · contradiction
  · simp only [Option.some.injEq] at selected
    subst gate
    simp only [reversibleGateWires, List.mem_singleton] at wireMember
    subst wire
    exact controlsMember control controlMember

/-- AND chainはprevious・controls・scratch・targetを含むsupport内だけを使う。 -/
theorem circuitUsesOnly_andChainUse
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (previous : Wire ancillaQubits systemQubits)
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (previousMember : previous ∈ support)
    (controlsMember : ∀ wire ∈ controls, wire ∈ support)
    (scratchMember : ∀ wire ∈ scratches, wire ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (andChainUse previous controls scratches target) := by
  induction controls generalizing previous scratches with
  | nil =>
      simp only [andChainUse]
      exact circuitUsesOnly_safeCnot support previous target
        previousMember targetMember
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil => simp [andChainUse, circuitUsesOnly]
      | cons scratch scratches =>
          simp only [andChainUse]
          have controlMember : control ∈ support := controlsMember control (by simp)
          have scratchHeadMember : scratch ∈ support := scratchMember scratch (by simp)
          have stepUses := circuitUsesOnly_safeToffoli support previous control scratch
            previousMember controlMember scratchHeadMember
          exact ⟨stepUses,
            ⟨inductionHypothesis scratch scratches scratchHeadMember
                (by
                  intro wire member
                  exact controlsMember wire (by simp [member]))
                (by
                  intro wire member
                  exact scratchMember wire (by simp [member])),
              stepUses⟩⟩

/-- 正制御多重Xはcontrols・scratch・targetを含むsupport内だけを使う。 -/
theorem circuitUsesOnly_positiveMultiControlledX
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (controls scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (controlsMember : ∀ wire ∈ controls, wire ∈ support)
    (scratchMember : ∀ wire ∈ scratches, wire ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (positiveMultiControlledX controls scratches target) := by
  cases controls with
  | nil =>
      exact circuitUsesOnly_x support target targetMember
  | cons control controls =>
      cases controls with
      | nil =>
          exact circuitUsesOnly_safeCnot support control target
            (controlsMember control (by simp)) targetMember
      | cons control₂ controls =>
          cases scratches with
          | nil => simp [positiveMultiControlledX, circuitUsesOnly]
          | cons scratch scratches =>
              have firstMember : control ∈ support := controlsMember control (by simp)
              have secondMember : control₂ ∈ support := controlsMember control₂ (by simp)
              have scratchHeadMember : scratch ∈ support := scratchMember scratch (by simp)
              let first := safeToffoli control control₂ scratch
              have firstUses : circuitUsesOnly support first :=
                circuitUsesOnly_safeToffoli support control control₂ scratch
                  firstMember secondMember scratchHeadMember
              exact ⟨firstUses,
                ⟨circuitUsesOnly_andChainUse support scratch controls scratches target
                    scratchHeadMember
                    (by
                      intro wire member
                      exact controlsMember wire (by simp [member]))
                    (by
                      intro wire member
                      exact scratchMember wire (by simp [member]))
                    targetMember,
                  firstUses⟩⟩

/-- Bool値付き多重Xはcontrols・scratch・targetを含むsupport内だけを使う。 -/
theorem circuitUsesOnly_boolMultiControlledX
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (controlsMember : ∀ control ∈ controls, control.1 ∈ support)
    (scratchMember : ∀ wire ∈ scratches, wire ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (boolMultiControlledX controls scratches target) := by
  let invert := invertZeroControls controls
  have invertUses : circuitUsesOnly support invert :=
    circuitUsesOnly_invertZeroControls support controls controlsMember
  have positiveUses : circuitUsesOnly support
      (positiveMultiControlledX (controls.map Prod.fst) scratches target) := by
    apply circuitUsesOnly_positiveMultiControlledX support _ scratches target
    · intro wire member
      rcases List.mem_map.mp member with ⟨control, controlMember, rfl⟩
      exact controlsMember control controlMember
    · exact scratchMember
    · exact targetMember
  exact ⟨invertUses, ⟨positiveUses, invertUses⟩⟩

/-- 一bit等値flag計算は左右bitとflagを含むsupport内だけを使う。 -/
theorem circuitUsesOnly_computeBitEqual
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (left right flag : Wire ancillaQubits systemQubits)
    (leftMember : left ∈ support) (rightMember : right ∈ support)
    (flagMember : flag ∈ support) :
    circuitUsesOnly support (computeBitEqual left right flag) := by
  exact ⟨circuitUsesOnly_safeCnot support left flag leftMember flagMember,
    ⟨circuitUsesOnly_safeCnot support right flag rightMember flagMember,
      circuitUsesOnly_x support flag flagMember⟩⟩

/-- bit列等値flag計算は左右wordとflag列を含むsupport内だけを使う。 -/
theorem circuitUsesOnly_computeEqualityFlags
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ (left right flags : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ left, wire ∈ support) →
      (∀ wire ∈ right, wire ∈ support) →
      (∀ wire ∈ flags, wire ∈ support) →
      circuitUsesOnly support (computeEqualityFlags left right flags)
  | [], _, _, _, _, _ => by
      change True
      trivial
  | _ :: _, [], _, _, _, _ => by
      change True
      trivial
  | _ :: _, _ :: _, [], _, _, _ => by
      change True
      trivial
  | leftBit :: left, rightBit :: right, flag :: flags,
      leftMembers, rightMembers, flagMembers => by
      change
        circuitUsesOnly support (computeBitEqual leftBit rightBit flag) ∧
          circuitUsesOnly support (computeEqualityFlags left right flags)
      constructor
      · exact circuitUsesOnly_computeBitEqual support leftBit rightBit flag
          (leftMembers leftBit (by simp))
          (rightMembers rightBit (by simp))
          (flagMembers flag (by simp))
      · exact circuitUsesOnly_computeEqualityFlags support left right flags
          (by
            intro wire member
            exact leftMembers wire (by simp [member]))
          (by
            intro wire member
            exact rightMembers wire (by simp [member]))
          (by
            intro wire member
            exact flagMembers wire (by simp [member]))

/-- 比較制御programに現れるwireは左右wordまたは等値flagのいずれかに属する。 -/
theorem lessThanControlProgram_wire_mem
    {ancillaQubits systemQubits : Nat} :
    ∀ (left right equalFlags : List (Wire ancillaQubits systemQubits))
      (controls : List (Wire ancillaQubits systemQubits × Bool)),
      controls ∈ lessThanControlProgram left right equalFlags →
      ∀ control ∈ controls, control.1 ∈ left ++ right ++ equalFlags
  | [], _, _, _, member => by simp [lessThanControlProgram] at member
  | _ :: _, [], _, _, member => by simp [lessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls, member => by
      simp only [lessThanControlProgram, List.mem_cons] at member
      rcases member with rfl | tailMember
      · intro control controlMember
        simp only [List.mem_cons] at controlMember
        rcases controlMember with rfl | controlMember
        · simp
        · rcases controlMember with rfl | higherMember
          · simp
          · rcases List.mem_map.mp higherMember with ⟨wire, wireMember, rfl⟩
            have originalMember : wire ∈ equalFlags :=
              List.mem_of_mem_drop wireMember
            simp [originalMember]
      · intro control controlMember
        have tailResult := lessThanControlProgram_wire_mem left right
          (equalFlags.drop 1) controls tailMember control controlMember
        rcases List.mem_append.mp tailResult with leftRightMember | flagMember
        · rcases List.mem_append.mp leftRightMember with leftMember | rightMember
          · simp [leftMember]
          · simp [rightMember]
        · have originalMember : control.1 ∈ equalFlags :=
            List.mem_of_mem_drop flagMember
          simp [originalMember]

/-- 一般little-endian比較器は指定した全入出力・work support内だけを使う。 -/
theorem circuitUsesOnly_lessThan
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (leftMembers : ∀ wire ∈ left, wire ∈ support)
    (rightMembers : ∀ wire ∈ right, wire ∈ support)
    (flagMembers : ∀ wire ∈ equalFlags, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratches, wire ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (xorLessThanIntoTargetCircuit left right equalFlags scratches target) := by
  let compute := computeEqualityFlags left right equalFlags
  let program := lessThanControlProgram left right equalFlags
  let branches := Circuit.sequence <| program.map fun controls =>
    boolMultiControlledX controls scratches target
  have computeUses : circuitUsesOnly support compute :=
    circuitUsesOnly_computeEqualityFlags support left right equalFlags
      leftMembers rightMembers flagMembers
  have branchesUse : circuitUsesOnly support branches := by
    apply circuitUsesOnly_sequence support
    intro branch branchMember
    rcases List.mem_map.mp branchMember with ⟨controls, controlsMember, rfl⟩
    apply circuitUsesOnly_boolMultiControlledX support controls scratches target
    · intro control controlMember
      have sourceMember := lessThanControlProgram_wire_mem left right equalFlags
        controls controlsMember control controlMember
      rcases List.mem_append.mp sourceMember with leftRightMember | flagMember
      · rcases List.mem_append.mp leftRightMember with leftMember | rightMember
        · exact leftMembers control.1 leftMember
        · exact rightMembers control.1 rightMember
      · exact flagMembers control.1 flagMember
    · exact scratchMembers
    · exact targetMember
  exact ⟨computeUses, ⟨branchesUse,
    circuitUsesOnly_reverse_id support compute computeUses⟩⟩

end ReversibleCircuit

end ProbabilityGeneratorQProof
