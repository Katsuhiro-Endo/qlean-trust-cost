import QLean.History.Implementation.HistoryPipelineFiniteScientificH3

set_option autoImplicit false
set_option warningAsError true

/-!
# Finite scientific history bridge

Connect the data-driven finite history word to the certified scientific word
one child at a time. Equality of the entire parameter records is deliberately
not assumed: their analytic fields have different roles. This module begins
with the exact selector child, including the carrier-width transport.
-/

namespace ExecutableHistoryFiniteScientificBridge

open VerifiedCircuitCore
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryFiniteScientificH3
open ExecutableHistoryFiniteScientificLayout
open ExecutableHistoryFiniteScientificAngles
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components

private theorem selectorExt {qubits : Nat}
    (left right : HistorySelectorPreparationParameters qubits)
    (low : left.low = right.low)
    (high : left.high = right.high)
    (firstHigh : left.firstHighAngle = right.firstHighAngle)
    (firstLow : left.firstLowAngle = right.firstLowAngle)
    (secondLow : left.secondLowAngle = right.secondLowAngle) : left = right := by
  cases left with
  | mk leftLow leftHigh leftDifferent leftFirstHigh leftFirstLow leftSecondLow =>
    cases right with
    | mk rightLow rightHigh rightDifferent rightFirstHigh rightFirstLow rightSecondLow =>
      dsimp at low high firstHigh firstLow secondLow
      subst rightLow
      subst rightHigh
      subst rightFirstHigh
      subst rightFirstLow
      subst rightSecondLow
      rfl

private theorem selectorCastLow {n m : Nat} (h : n = m)
    (selector : HistorySelectorPreparationParameters n) :
    (h ▸ selector).low = Fin.cast h selector.low := by
  cases h
  rfl

private theorem selectorCastHigh {n m : Nat} (h : n = m)
    (selector : HistorySelectorPreparationParameters n) :
    (h ▸ selector).high = Fin.cast h selector.high := by
  cases h
  rfl

private theorem selectorCastFirstHigh {n m : Nat} (h : n = m)
    (selector : HistorySelectorPreparationParameters n) :
    (h ▸ selector).firstHighAngle = selector.firstHighAngle := by
  cases h
  rfl

private theorem selectorCastFirstLow {n m : Nat} (h : n = m)
    (selector : HistorySelectorPreparationParameters n) :
    (h ▸ selector).firstLowAngle = selector.firstLowAngle := by
  cases h
  rfl

private theorem selectorCastSecondLow {n m : Nat} (h : n = m)
    (selector : HistorySelectorPreparationParameters n) :
    (h ▸ selector).secondLowAngle = selector.secondLowAngle := by
  cases h
  rfl

/-- The emitted selector data agree with the certified selector after the
scientific carrier-width equality is applied. -/
theorem finiteScientificSelector_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteScientificHistoryQubits119_eq source) ▸
      (finiteScientificCorrectedP05Plan119 source).selector =
        (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).selector := by
  let hWidth := finiteScientificHistoryQubits119_eq source
  apply selectorExt
  · rw [selectorCastLow]
    apply Fin.ext
    exact finiteScientificHistorySelectorWire119_scientific_val source domain
      ⟨0, by decide⟩
  · rw [selectorCastHigh]
    apply Fin.ext
    exact finiteScientificHistorySelectorWire119_scientific_val source domain
      ⟨1, by decide⟩
  · rw [selectorCastFirstHigh]
    rfl
  · rw [selectorCastFirstLow]
    rfl
  · rw [selectorCastSecondLow]
    rfl

/-- The certified parameter record is used only as a type index in the
following retyping step. Its analytic entries remain those of the scientific
specification; the finite compiler does not replace them with neutral data. -/
noncomputable def certifiedParameters
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryBlockParameters :=
  HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic

/-- The finite and certified layouts have definitionally identical integer
shape indices. Copying the finite wires into the scientific parameter index
therefore requires no assumptions about the analytic entries. -/
noncomputable def retypedFiniteLayout
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryBlockLayout
      (finiteScientificHistoryQubits119 source)
      source.qParameters.generatorDataWidth
      source.qParameters.generatorSignalWidth
      (historyClockWorkspaceWidth (certifiedParameters source domain)
        source.qParameters.generatorWorkWidth)
      (certifiedParameters source domain) :=
  let layout := finiteScientificHistoryLayout119 source
  { selector := layout.selector
    data := layout.data
    clock := layout.clock
    order := layout.order
    generatorSignal := layout.generatorSignal
    coefficientSignal := layout.coefficientSignal
    orderBoundarySignal := layout.orderBoundarySignal
    projectorSignal := layout.projectorSignal
    clockBoundarySignal := layout.clockBoundarySignal
    workspace := layout.workspace
    allWiresNodup := layout.allWiresNodup }

def castHistoryLayout
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (qubitsEq : q₁ = q₂) (dataEq : d₁ = d₂)
    (signalEq : s₁ = s₂) (workEq : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters) :
    HistoryBlockLayout q₂ d₂ s₂
      (historyClockWorkspaceWidth parameters w₂) parameters := by
  cases qubitsEq
  cases dataEq
  cases signalEq
  cases workEq
  exact layout

/-- The retyped finite layout also inhabits the certified carrier and
register widths. This is a change of indices, not an assertion that the
analytic parameter records are equal. -/
noncomputable def retypedFiniteLayoutAtCertifiedWidth
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryBlockLayout
      (ExecutableRaw119 source).history.qubits
      (ExecutableRaw119 source).history.dataWidth
      (ExecutableRaw119 source).history.generatorSignalWidth
      (historyClockWorkspaceWidth (certifiedParameters source domain)
        (ExecutableRaw119 source).history.generatorWorkWidth)
      (certifiedParameters source domain) :=
  castHistoryLayout
    (finiteScientificHistoryQubits119_eq source)
    (executableHistory_dataWidth119 source).symm
    (executableHistory_signalWidth119 source).symm
    (executableHistory_workWidth119 source).symm
    (retypedFiniteLayout source domain)

private theorem castHistoryLayout_selector_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (bit : Fin 2) :
    ((castHistoryLayout hq hd hs hw layout).selector.wire bit).val =
      (layout.selector.wire bit).val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_data_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (bit : Fin d₁) :
    ((castHistoryLayout hq hd hs hw layout).data.wire
      (Fin.cast hd bit)).val = (layout.data.wire bit).val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_clock_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (bit : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    ((castHistoryLayout hq hd hs hw layout).clock.wire bit).val =
      (layout.clock.wire bit).val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_order_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (bit : Fin (historyOrderWidth parameters.taylorOrder)) :
    ((castHistoryLayout hq hd hs hw layout).order.wire bit).val =
      (layout.order.wire bit).val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_signal_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (bit : Fin s₁) :
    ((castHistoryLayout hq hd hs hw layout).generatorSignal.wire
      (Fin.cast hs bit)).val = (layout.generatorSignal.wire bit).val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_workspace_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (bit : Fin (historyClockWorkspaceWidth parameters w₁)) :
    ((castHistoryLayout hq hd hs hw layout).workspace.wire
      (Fin.cast (congrArg (historyClockWorkspaceWidth parameters) hw)
        bit)).val = (layout.workspace.wire bit).val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_coefficient_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters) :
    (castHistoryLayout hq hd hs hw layout).coefficientSignal.val =
      layout.coefficientSignal.val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_orderBoundary_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters) :
    (castHistoryLayout hq hd hs hw layout).orderBoundarySignal.val =
      layout.orderBoundarySignal.val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_projector_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters) :
    (castHistoryLayout hq hd hs hw layout).projectorSignal.val =
      layout.projectorSignal.val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem castHistoryLayout_clockBoundary_val
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂)
    (hw : w₁ = w₂)
    (layout : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters) :
    (castHistoryLayout hq hd hs hw layout).clockBoundarySignal.val =
      layout.clockBoundarySignal.val := by
  cases hq
  cases hd
  cases hs
  cases hw
  rfl

private theorem registerExt {qubits width : Nat}
    (left right : Register qubits width)
    (wireEq : ∀ index, left.wire index = right.wire index) :
    left = right := by
  cases left with
  | mk leftWire leftInjective =>
    cases right with
    | mk rightWire rightInjective =>
      have hWire : leftWire = rightWire := funext wireEq
      subst rightWire
      rfl

private theorem layoutExt
    {qubits dataWidth signalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (left right : HistoryBlockLayout qubits dataWidth signalWidth
      workspaceWidth parameters)
    (selectorEq : left.selector = right.selector)
    (dataEq : left.data = right.data)
    (clockEq : left.clock = right.clock)
    (orderEq : left.order = right.order)
    (generatorSignalEq : left.generatorSignal = right.generatorSignal)
    (coefficientEq : left.coefficientSignal = right.coefficientSignal)
    (orderBoundaryEq : left.orderBoundarySignal = right.orderBoundarySignal)
    (projectorEq : left.projectorSignal = right.projectorSignal)
    (clockBoundaryEq : left.clockBoundarySignal = right.clockBoundarySignal)
    (workspaceEq : left.workspace = right.workspace) : left = right := by
  cases left with
  | mk ls ld lc lo lg lcoeff lobound lproj lcbound lw lproof =>
    cases right with
    | mk rs rd rc ro rg rcoeff robound rproj rcbound rw rproof =>
      dsimp at selectorEq dataEq clockEq orderEq generatorSignalEq
      dsimp at coefficientEq orderBoundaryEq projectorEq clockBoundaryEq workspaceEq
      subst rs
      subst rd
      subst rc
      subst ro
      subst rg
      subst rcoeff
      subst robound
      subst rproj
      subst rcbound
      subst rw
      rfl

/-- The scientific finite plan and certified plan place every register and
distinguished signal on exactly the same physical wires. The analytic
parameter fields are kept separate; only their shared integer indices and
the actual wire maps are compared here. -/
theorem retypedFiniteLayout_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    retypedFiniteLayoutAtCertifiedWidth source domain =
      ExecutableLayout119 source domain := by
  apply layoutExt
  · apply registerExt
    intro bit
    apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth,
      castHistoryLayout_selector_val]
    exact finiteScientificHistorySelectorWire119_scientific_val source domain bit
  · apply registerExt
    intro bit
    let sourceBit := Fin.cast (executableHistory_dataWidth119 source) bit
    have hWire :
        (retypedFiniteLayoutAtCertifiedWidth source domain).data.wire
          (Fin.cast (executableHistory_dataWidth119 source).symm sourceBit) =
        (ExecutableLayout119 source domain).data.wire
          (Fin.cast (executableHistory_dataWidth119 source).symm sourceBit) := by
      apply Fin.ext
      rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_data_val]
      exact finiteScientificHistoryDataWire119_scientific_val
        source domain sourceBit
    have castBack :
        Fin.cast (executableHistory_dataWidth119 source).symm sourceBit =
          bit := by
      apply Fin.ext
      rfl
    exact (congrArg
      (retypedFiniteLayoutAtCertifiedWidth source domain).data.wire
      castBack.symm).trans
      (hWire.trans (congrArg
        (ExecutableLayout119 source domain).data.wire castBack))
  · apply registerExt
    intro bit
    apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth,
      castHistoryLayout_clock_val]
    exact finiteScientificHistoryClockWire119_scientific_val source domain bit
  · apply registerExt
    intro bit
    apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth,
      castHistoryLayout_order_val]
    exact finiteScientificHistoryOrderWire119_scientific_val source domain bit
  · apply registerExt
    intro bit
    let sourceBit := Fin.cast (executableHistory_signalWidth119 source) bit
    have hWire :
        (retypedFiniteLayoutAtCertifiedWidth source domain).generatorSignal.wire
          (Fin.cast (executableHistory_signalWidth119 source).symm sourceBit) =
        (ExecutableLayout119 source domain).generatorSignal.wire
          (Fin.cast (executableHistory_signalWidth119 source).symm sourceBit) := by
      apply Fin.ext
      rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_signal_val]
      exact finiteScientificHistoryGeneratorSignalWire119_scientific_val
        source domain sourceBit
    have castBack :
        Fin.cast (executableHistory_signalWidth119 source).symm sourceBit =
          bit := by
      apply Fin.ext
      rfl
    exact (congrArg
      (retypedFiniteLayoutAtCertifiedWidth source domain).generatorSignal.wire
      castBack.symm).trans
      (hWire.trans (congrArg
        (ExecutableLayout119 source domain).generatorSignal.wire castBack))
  · apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_coefficient_val]
    exact finiteScientificHistoryDistinguishedSignalWire119_scientific_val
      source ⟨0, by decide⟩
  · apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_orderBoundary_val]
    exact finiteScientificHistoryDistinguishedSignalWire119_scientific_val
      source ⟨1, by decide⟩
  · apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_projector_val]
    exact finiteScientificHistoryDistinguishedSignalWire119_scientific_val
      source ⟨2, by decide⟩
  · apply Fin.ext
    rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_clockBoundary_val]
    exact finiteScientificHistoryDistinguishedSignalWire119_scientific_val
      source ⟨3, by decide⟩
  · apply registerExt
    intro bit
    let hWork := congrArg
      (historyClockWorkspaceWidth (certifiedParameters source domain))
      (executableHistory_workWidth119 source)
    let sourceBit := Fin.cast hWork bit
    have hWire :
        (retypedFiniteLayoutAtCertifiedWidth source domain).workspace.wire
          (Fin.cast hWork.symm sourceBit) =
        (ExecutableLayout119 source domain).workspace.wire
          (Fin.cast hWork.symm sourceBit) := by
      apply Fin.ext
      rw [retypedFiniteLayoutAtCertifiedWidth, castHistoryLayout_workspace_val]
      exact finiteScientificHistoryWorkspaceWire119_scientific_val
        source domain sourceBit
    have castBack : Fin.cast hWork.symm sourceBit = bit := by
      apply Fin.ext
      rfl
    exact (congrArg
      (retypedFiniteLayoutAtCertifiedWidth source domain).workspace.wire
      castBack.symm).trans
      (hWire.trans (congrArg
        (ExecutableLayout119 source domain).workspace.wire castBack))

noncomputable def retypedClockEvidence
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryClockConcreteSourceOrderEvidence
      (retypedFiniteLayout source domain) :=
  let evidence := finiteH3SourceOrderEvidence119 source
  { uniformExternalControl := {
      active_ne_order := evidence.uniformExternalControl.active_ne_order
      work₀_ne_active := evidence.uniformExternalControl.work₀_ne_active
      work₁_ne_active := evidence.uniformExternalControl.work₁_ne_active
      work₀_ne_order := evidence.uniformExternalControl.work₀_ne_order
      work₁_ne_order := evidence.uniformExternalControl.work₁_ne_order }
    idleTransform := {
      idleEnd_ne_idle := evidence.idleTransform.idleEnd_ne_idle
      time_ne_idle := evidence.idleTransform.time_ne_idle
      active_ne_order := evidence.idleTransform.active_ne_order
      active_ne_coefficient := evidence.idleTransform.active_ne_coefficient }
    coefficientControl_ne_signal := evidence.coefficientControl_ne_signal
    projectorControl := {
      branch_ne_projector := evidence.projectorControl.branch_ne_projector
      coefficientControl_ne_projector :=
        evidence.projectorControl.coefficientControl_ne_projector }
    controlledIncrement := {
      masked_clock_disjoint := evidence.controlledIncrement.masked_clock_disjoint
      carry_ne_masked := evidence.controlledIncrement.carry_ne_masked
      carry_ne_clock := evidence.controlledIncrement.carry_ne_clock
      branch_ne_masked := evidence.controlledIncrement.branch_ne_masked
      branch_ne_clock := evidence.controlledIncrement.branch_ne_clock
      branch_ne_carry := evidence.controlledIncrement.branch_ne_carry }
    idleCoefficientAngle := evidence.idleCoefficientAngle
    coefficientAngle := evidence.coefficientAngle }

/-- Changing only the analytic fields of the history parameter record does
not alter the generated repaired-H3 circuit. -/
theorem finiteScientificH3_retyped
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    finiteScientificRepairedH3Circuit119 source =
      finiteRepairedH3Circuit119 (retypedFiniteLayout source domain)
        (retypedClockEvidence source domain)
        (finiteClockTimeComparison119 source)
        (finiteClockIdleEndComparison119 source)
        source.historyParameters.physicalClocks
        (historyIdleClockEnd source.historyParameters.physicalClocks
          source.historyParameters.taylorOrder
          (finiteScientificHistoryIdleSteps119 source))
        source.historyParameters.binaryLabels
        (repairedIdle source) idleCoefficient := by
  rfl

noncomputable def retypedL2Evidence
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryTaylorL2Evidence (retypedFiniteLayout source domain) :=
  let evidence := finiteHistoryTaylorL2Evidence119 source
  { clockTimeLessThan := {
      widthPositive := evidence.clockTimeLessThan.widthPositive
      lhsRhsDifferent := evidence.clockTimeLessThan.lhsRhsDifferent
      lhsBorrowDifferent := evidence.clockTimeLessThan.lhsBorrowDifferent
      rhsBorrowDifferent := evidence.clockTimeLessThan.rhsBorrowDifferent
      targetLhsDifferent := evidence.clockTimeLessThan.targetLhsDifferent
      targetRhsDifferent := evidence.clockTimeLessThan.targetRhsDifferent
      targetBorrowDifferent := evidence.clockTimeLessThan.targetBorrowDifferent }
    clockIdleEndLessThan := {
      widthPositive := evidence.clockIdleEndLessThan.widthPositive
      lhsRhsDifferent := evidence.clockIdleEndLessThan.lhsRhsDifferent
      lhsBorrowDifferent := evidence.clockIdleEndLessThan.lhsBorrowDifferent
      rhsBorrowDifferent := evidence.clockIdleEndLessThan.rhsBorrowDifferent
      targetLhsDifferent := evidence.clockIdleEndLessThan.targetLhsDifferent
      targetRhsDifferent := evidence.clockIdleEndLessThan.targetRhsDifferent
      targetBorrowDifferent := evidence.clockIdleEndLessThan.targetBorrowDifferent }
    degreeOrderLessThan := {
      widthPositive := evidence.degreeOrderLessThan.widthPositive
      lhsRhsDifferent := evidence.degreeOrderLessThan.lhsRhsDifferent
      lhsBorrowDifferent := evidence.degreeOrderLessThan.lhsBorrowDifferent
      rhsBorrowDifferent := evidence.degreeOrderLessThan.rhsBorrowDifferent
      targetLhsDifferent := evidence.degreeOrderLessThan.targetLhsDifferent
      targetRhsDifferent := evidence.degreeOrderLessThan.targetRhsDifferent
      targetBorrowDifferent := evidence.degreeOrderLessThan.targetBorrowDifferent }
    degreeIncrement := {
      addend_accumulator_disjoint := evidence.degreeIncrement.addend_accumulator_disjoint
      carry_ne_addend := evidence.degreeIncrement.carry_ne_addend
      carry_ne_accumulator := evidence.degreeIncrement.carry_ne_accumulator
      control_ne_addend := evidence.degreeIncrement.control_ne_addend
      control_ne_accumulator := evidence.degreeIncrement.control_ne_accumulator
      control_ne_carry := evidence.degreeIncrement.control_ne_carry }
    branch_ne_ltIdleEnd := evidence.branch_ne_ltIdleEnd
    branch_ne_coefficientSignal := evidence.branch_ne_coefficientSignal
    ltIdleEnd_ne_coefficientSignal := evidence.ltIdleEnd_ne_coefficientSignal
    active_ne_equality := evidence.active_ne_equality
    active_ne_orderBoundary := evidence.active_ne_orderBoundary
    equality_ne_orderBoundary := evidence.equality_ne_orderBoundary
    ltIdleEnd_ne_idle := evidence.ltIdleEnd_ne_idle
    ltTime_ne_idle := evidence.ltTime_ne_idle
    active_ne_coefficientSignal := evidence.active_ne_coefficientSignal
    coefficientControl_ne_coefficientSignal :=
      evidence.coefficientControl_ne_coefficientSignal
    coefficientAngles := evidence.coefficientAngles
    idleCoefficientAngle := evidence.idleCoefficientAngle }

/-- The complete finite P15 word likewise depends on the integer shape,
wire placement and explicit angles, not the parameter record's analytic
fields. -/
theorem finiteScientificP15_retyped
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    finiteScientificTaylorCircuit119 source =
      finiteHistoryTaylorPaddedCircuit119 source.qParameters
        (retypedFiniteLayout source domain)
        (retypedL2Evidence source domain)
        (finiteHistoryQ10ControlEvidence119 source)
        (fun index => correctedCoefficient source index.val)
        idleCoefficient := by
  rfl

end ExecutableHistoryFiniteScientificBridge
