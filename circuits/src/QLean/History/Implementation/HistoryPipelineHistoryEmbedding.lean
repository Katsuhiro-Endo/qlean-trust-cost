import QLean.History.Implementation.HistoryPipelineExecutableP05Target
import QLean.History.Implementation.HistoryPipelineReferenceM10Bridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryHistoryEmbedding

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open HistoryBlockEncoding
open ExecutableHistoryExecutableHistory

noncomputable section

abbrev OldHistoryIndex119 (source : AlignedCommonSource119) :=
  HistorySpec.Index (QConfiguration source.qParameters)
    source.historyParameters

/-- The old mathematical carrier must fit in the physical clock/order
registers.  This is a representation-capacity condition, not a target or
operator equality premise. -/
structure HistoryIndexFitsLayout119 (source : AlignedCommonSource119) : Prop where
  clock_fits : source.historyParameters.clockEnd <
    2 ^ historyClockWidth source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder - 1)
  label_fits : source.historyParameters.binaryLabels ≤
    2 ^ historyOrderWidth source.historyParameters.taylorOrder

theorem data_wire_ne_clock_wire119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (dataIndex : Fin (ExecutableRaw119 source).history.dataWidth)
    (clockIndex : Fin (historyClockWidth
      source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder - 1))) :
    (ExecutableLayout119 source domain).data.wire dataIndex ≠
      (ExecutableLayout119 source domain).clock.wire clockIndex := by
  intro equal
  have selected :
      (historyRegisterWires (ExecutableLayout119 source domain).data ++
        historyRegisterWires (ExecutableLayout119 source domain).clock).Nodup :=
    List.Nodup.sublist (by simp)
      (ExecutableLayout119 source domain).allWiresNodup
  have dataMember : (ExecutableLayout119 source domain).data.wire dataIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).data :=
    List.mem_ofFn.mpr <| Exists.intro dataIndex rfl
  have clockMember : (ExecutableLayout119 source domain).clock.wire clockIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).clock :=
    List.mem_ofFn.mpr <| Exists.intro clockIndex rfl
  have separated := (List.nodup_append.mp selected).2.2
  exact (separated _ dataMember _ clockMember) equal

theorem data_wire_ne_order_wire119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (dataIndex : Fin (ExecutableRaw119 source).history.dataWidth)
    (orderIndex : Fin (historyOrderWidth
      source.historyParameters.taylorOrder)) :
    (ExecutableLayout119 source domain).data.wire dataIndex ≠
      (ExecutableLayout119 source domain).order.wire orderIndex := by
  intro equal
  have selected :
      (historyRegisterWires (ExecutableLayout119 source domain).data ++
        (historyRegisterWires (ExecutableLayout119 source domain).clock ++
          historyRegisterWires (ExecutableLayout119 source domain).order)).Nodup :=
    List.Nodup.sublist (by simp)
      (ExecutableLayout119 source domain).allWiresNodup
  have dataMember : (ExecutableLayout119 source domain).data.wire dataIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).data :=
    List.mem_ofFn.mpr <| Exists.intro dataIndex rfl
  have orderMember : (ExecutableLayout119 source domain).order.wire orderIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).order :=
    List.mem_ofFn.mpr <| Exists.intro orderIndex rfl
  have separated := (List.nodup_append.mp selected).2.2
  have tailMember : (ExecutableLayout119 source domain).order.wire orderIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).clock ++
        historyRegisterWires (ExecutableLayout119 source domain).order := by
    simp [orderMember]
  exact (separated _ dataMember _ tailMember) equal

theorem clock_wire_ne_order_wire119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (clockIndex : Fin (historyClockWidth
      source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder - 1)))
    (orderIndex : Fin (historyOrderWidth
      source.historyParameters.taylorOrder)) :
    (ExecutableLayout119 source domain).clock.wire clockIndex ≠
      (ExecutableLayout119 source domain).order.wire orderIndex := by
  intro equal
  have selected :
      (historyRegisterWires (ExecutableLayout119 source domain).data ++
        (historyRegisterWires (ExecutableLayout119 source domain).clock ++
          historyRegisterWires (ExecutableLayout119 source domain).order)).Nodup :=
    List.Nodup.sublist (by simp)
      (ExecutableLayout119 source domain).allWiresNodup
  have clockMember : (ExecutableLayout119 source domain).clock.wire clockIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).clock :=
    List.mem_ofFn.mpr <| Exists.intro clockIndex rfl
  have orderMember : (ExecutableLayout119 source domain).order.wire orderIndex ∈
      historyRegisterWires (ExecutableLayout119 source domain).order :=
    List.mem_ofFn.mpr <| Exists.intro orderIndex rfl
  have tailNodup := (List.nodup_append.mp selected).2.1
  have separated := (List.nodup_append.mp tailNodup).2.2
  exact (separated _ clockMember _ orderMember) equal

theorem executableHistory_dataWidth_eq_system119
    (source : AlignedCommonSource119) :
    (ExecutableRaw119 source).history.dataWidth =
      source.qParameters.systemWidth := by
  change (executableHistoryRaw119 source).dataWidth =
    source.qParameters.systemWidth
  rw [executableHistory_dataWidth119]
  exact QParameters.generatorDataWidth_eq_systemWidth source.qParameters

def dataIndexCast119
    (source : AlignedCommonSource119) :
    Fin (ExecutableRaw119 source).history.dataWidth ->
      Fin source.qParameters.systemWidth :=
  Fin.cast (executableHistory_dataWidth_eq_system119 source)

def dataBits119
    (source : AlignedCommonSource119)
    (configuration : QConfiguration source.qParameters) :
    QubitBasis (ExecutableRaw119 source).history.dataWidth :=
  fun index => delimiterEncoding configuration (dataIndexCast119 source index)

theorem dataBits119_injective
    (source : AlignedCommonSource119) :
    Function.Injective (dataBits119 source) := by
  intro left right equal
  apply delimiterEncoding_injective
  funext index
  have atCast := congrFun equal
    (Fin.cast (executableHistory_dataWidth_eq_system119 source).symm index)
  simpa [dataBits119, dataIndexCast119] using atCast

def clockBits119
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    QubitBasis (historyClockWidth source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder - 1)) :=
  qubitBasisOfLittleEndianIndex
    { val := index.clock.val
      isLt := lt_trans index.clock.isLt fits.clock_fits }

def orderBits119
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    QubitBasis (historyOrderWidth source.historyParameters.taylorOrder) :=
  qubitBasisOfLittleEndianIndex
    { val := index.state.label.val
      isLt := lt_of_lt_of_le index.state.label.isLt fits.label_fits }

/-- Logical history basis encoded in the actual P05 layout.  Selector,
signals and work start at zero; only data, clock and order are written. -/
def executableHistoryBasis119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    QubitBasis (ExecutableRaw119 source).history.qubits :=
  writeRegisterBits (ExecutableLayout119 source domain).data
    (dataBits119 source index.state.configuration)
    (writeRegisterBits (ExecutableLayout119 source domain).clock
      (clockBits119 source fits index)
      (writeRegisterBits (ExecutableLayout119 source domain).order
        (orderBits119 source fits index) (fun _ => false)))

theorem executableHistoryBasis119_read_data
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    (ExecutableLayout119 source domain).data.read
        (executableHistoryBasis119 source domain fits index) =
      dataBits119 source index.state.configuration := by
  funext bit
  simp [executableHistoryBasis119, Register.read]

theorem executableHistoryBasis119_read_clock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    (ExecutableLayout119 source domain).clock.read
        (executableHistoryBasis119 source domain fits index) =
      clockBits119 source fits index := by
  funext bit
  unfold executableHistoryBasis119 Register.read
  rw [writeRegisterBits_apply_outside]
  · exact writeRegisterBits_apply_wire _ _ _ bit
  · intro dataIndex equal
    exact data_wire_ne_clock_wire119 source domain dataIndex bit equal

theorem executableHistoryBasis119_read_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    (ExecutableLayout119 source domain).order.read
        (executableHistoryBasis119 source domain fits index) =
      orderBits119 source fits index := by
  funext bit
  unfold executableHistoryBasis119 Register.read
  rw [writeRegisterBits_apply_outside]
  · rw [writeRegisterBits_apply_outside]
    · exact writeRegisterBits_apply_wire _ _ _ bit
    · intro clockIndex equal
      exact clock_wire_ne_order_wire119 source domain clockIndex bit equal
  · intro dataIndex equal
    exact data_wire_ne_order_wire119 source domain dataIndex bit equal

theorem labelState_ext119
    {Configuration : Type*} {parameters : HistorySpec.Parameters}
    (left right : HistorySpec.LabelState Configuration parameters)
    (labelEqual : left.label = right.label)
    (configurationEqual : left.configuration = right.configuration) :
    left = right := by
  cases left
  cases right
  simp_all

theorem oldHistoryIndex_ext119
    {Configuration : Type*} {parameters : HistorySpec.Parameters}
    (left right : HistorySpec.Index Configuration parameters)
    (clockEqual : left.clock = right.clock)
    (stateEqual : left.state = right.state) :
    left = right := by
  cases left
  cases right
  simp_all

theorem executableHistoryBasis119_injective
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    Function.Injective (executableHistoryBasis119 source domain fits) := by
  intro left right equal
  have dataEqual : dataBits119 source left.state.configuration =
      dataBits119 source right.state.configuration := by
    rw [← executableHistoryBasis119_read_data source domain fits left,
      ← executableHistoryBasis119_read_data source domain fits right, equal]
  have configurationEqual : left.state.configuration =
      right.state.configuration := dataBits119_injective source dataEqual
  have clockEqualBits : clockBits119 source fits left =
      clockBits119 source fits right := by
    rw [← executableHistoryBasis119_read_clock source domain fits left,
      ← executableHistoryBasis119_read_clock source domain fits right, equal]
  have clockEqual : left.clock = right.clock := by
    apply Fin.ext
    have decoded := congrArg
      (qubitBasisLittleEndianIndex
        (historyClockWidth source.historyParameters.physicalClocks
          source.historyParameters.taylorOrder
          (source.historyBlocks *
            historyIdleBlockSize source.historyParameters.taylorOrder - 1)))
      clockEqualBits
    dsimp [clockBits119] at decoded
    rw [qubitBasisLittleEndianIndex_basis,
      qubitBasisLittleEndianIndex_basis] at decoded
    exact decoded
  have orderEqualBits : orderBits119 source fits left =
      orderBits119 source fits right := by
    rw [← executableHistoryBasis119_read_order source domain fits left,
      ← executableHistoryBasis119_read_order source domain fits right, equal]
  have labelEqual : left.state.label = right.state.label := by
    apply Fin.ext
    have decoded := congrArg
      (qubitBasisLittleEndianIndex
        (historyOrderWidth source.historyParameters.taylorOrder))
      orderEqualBits
    dsimp [orderBits119] at decoded
    rw [qubitBasisLittleEndianIndex_basis,
      qubitBasisLittleEndianIndex_basis] at decoded
    exact decoded
  have stateEqual : left.state = right.state := by
    exact labelState_ext119 left.state right.state
      labelEqual configurationEqual
  exact oldHistoryIndex_ext119 left right clockEqual stateEqual

def executableHistoryEmbedding119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) :
    OldHistoryIndex119 source ↪
      QubitBasis (ExecutableRaw119 source).history.qubits where
  toFun := executableHistoryBasis119 source domain fits
  inj' := executableHistoryBasis119_injective source domain fits

end
end ExecutableHistoryHistoryEmbedding
