import QLean.History.Implementation.HistoryPipelineH3LiveFacts
import QLean.History.Implementation.HistoryPipelineInverseUniformEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

def h3ZeroOrder119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  writeRegisterValue layout.order 0 input

theorem uniformInverseStrict_zero_entry119
    {targetQubits : Nat}
    (parameters : UniformPreparationParameters)
    (layout : ExternallyControlledCircuitLayout parameters.width targetQubits)
    (valid : layout.CleanWorkValid)
    (output input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input)
    (active : input layout.control = true)
    (outputPlaced : restrictToPlacedWires layout.placement output =
      (fun _ => false))
    (outsideEqual : restrictToOutsideWires layout.placement output =
      restrictToOutsideWires layout.placement input) :
    ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
        layout (shuklaVedulaWidthOnlyUniformInversePlan parameters)
        output input =
      ((if qubitBasisLittleEndianIndex parameters.width
          (restrictToPlacedWires layout.placement input) <
          parameters.validCount then
        (1 / Real.sqrt parameters.validCount : ℝ)
      else 0 : ℝ) : Complex) := by
  rw [uniformInverseStrict_clean_entry119 parameters layout valid
    output input clean]
  unfold externallyControlledWireLiftOperator
  rw [if_pos active]
  rw [wireLiftOperator_apply, outputPlaced, outsideEqual]
  simp only [if_pos, mul_one]
  rw [← shuklaUniformInverseSourceOperator119 parameters]
  simpa using (shuklaUniformInverse_zero_entry119 parameters
    (restrictToPlacedWires layout.placement input))

theorem h3UniformInverse_zero_order_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout input
    (historyOrderUniformPreparationInverseExactComponent layout
      (ExecutableClockEvidence119 source domain).uniformExternalControl).target
        (h3ZeroOrder119 layout before) before =
      if index.state.label.val ≤ source.historyParameters.taylorOrder then
        (((1 / Real.sqrt (source.historyParameters.taylorOrder + 1) : Real) :
          Complex))
      else 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let blockParameters := HistoryRawSchema.parameters203
    (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic
  let parameters := historyOrderUniformPreparationParameters
    blockParameters
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout input
  let zero := h3ZeroOrder119 layout before
  have blockTaylor :
      blockParameters.taylorOrder =
        source.historyParameters.taylorOrder := by
    rfl
  have clean : externallyControlledCleanWorkPredicate
      (historyOrderUniformExternalControlCleanWorkValid layout evidence) before :=
    h3BeforeUniform119_uniform_work_clean source domain fits index
  have activeTrue : before (historyActiveWire layout) = true := by
    simpa [before, input, layout, clockActive] using
      h3BeforeUniform119_active_selected_value source domain fits index
  have activeControlled : before controlled.control = true := by
    simpa [controlled, historyOrderUniformExternalControlLayout] using activeTrue
  have outputPlaced : restrictToPlacedWires controlled.placement zero =
      (fun _ => false) := by
    funext orderIndex
    change zero (layout.order.wire orderIndex) = false
    simp [zero, h3ZeroOrder119]
  have inputPlacedValue :
      qubitBasisLittleEndianIndex parameters.width
          (restrictToPlacedWires controlled.placement before) =
        index.state.label.val := by
    change qubitBasisLittleEndianIndex
        (historyOrderWidth source.historyParameters.taylorOrder)
        (layout.order.read before) = index.state.label.val
    rw [h3BeforeUniform119_read_order,
      correctedBranchHistoryBasis119_read_order]
    dsimp only [orderBits119]
    exact qubitBasisLittleEndianIndex_basis _
  have outsideEqual :
      restrictToOutsideWires controlled.placement zero =
        restrictToOutsideWires controlled.placement before := by
    funext outside
    change zero outside.val = before outside.val
    apply writeRegisterValue_apply_outside
    intro orderIndex
    exact outside.property orderIndex
  rw [historyOrderUniformPreparationInverseExactComponent_target]
  have entry := uniformInverseStrict_zero_entry119
    parameters controlled
    (historyOrderUniformExternalControlCleanWorkValid layout evidence)
    zero before clean activeControlled outputPlaced outsideEqual
  have entryValue :
      ((if qubitBasisLittleEndianIndex parameters.width
            (restrictToPlacedWires controlled.placement before) <
            parameters.validCount then
          (1 / Real.sqrt parameters.validCount : ℝ)
        else 0 : ℝ) : Complex) =
        if index.state.label.val ≤ source.historyParameters.taylorOrder then
          (((1 / Real.sqrt
            (source.historyParameters.taylorOrder + 1) : ℝ) : Complex))
        else 0 := by
    rw [inputPlacedValue]
    dsimp [parameters, historyOrderUniformPreparationParameters]
    simp only [blockTaylor]
    by_cases inside :
        index.state.label.val ≤ source.historyParameters.taylorOrder
    · rw [if_pos inside, if_pos (by omega)]
      norm_num
    · rw [if_neg inside, if_neg (by omega)]
      norm_num
  exact entry.trans entryValue

end
end ExecutableHistoryExecutableHistory
