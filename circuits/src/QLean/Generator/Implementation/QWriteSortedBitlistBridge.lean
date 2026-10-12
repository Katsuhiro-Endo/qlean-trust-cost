import QLean.Generator.Implementation.QWriteSortedConfigurationBridge

/-!
# sorted writer と delimiter bit列の橋渡し

canonical candidate を読む有限foldの局所word仕様を、物理system添字ごとの作用へ持ち上げる。
巨大な基底列挙は行わず、除算・剰余によるword添字分解だけを用いる。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- canonical 出力registerを物理system添字で読む型安全なwire写像。 -/
def canonicalSortedOutputWireAt (p : QParameters)
    (kind : CanonicalSortedOutputKind) (physical : Fin p.systemWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (canonicalSortedOutputWires p kind).get ⟨physical.val, by
    rw [canonicalSortedOutputWires_length]
    exact physical.isLt⟩

/-- canonical register wordの局所bit読出しは、元registerの対応物理wire評価に一致する。 -/
theorem readWires_canonicalRegisterWord_getElem
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (slot : Fin p.K) (bit : Fin p.wordWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (readWires (registerWordAt p (canonicalSortedOutputWires p kind) slot)
      input)[bit.val]? =
    some (input ((canonicalSortedOutputWires p kind).get
      ⟨slot.val * p.wordWidth + bit.val, by
        rw [canonicalSortedOutputWires_length]
        simp only [QParameters.systemWidth]
        have slotNext : slot.val + 1 ≤ p.K := Nat.succ_le_of_lt slot.isLt
        calc
          slot.val * p.wordWidth + bit.val <
              slot.val * p.wordWidth + p.wordWidth :=
            Nat.add_lt_add_left bit.isLt _
          _ = (slot.val + 1) * p.wordWidth := by rw [Nat.succ_mul]
          _ ≤ p.K * p.wordWidth := Nat.mul_le_mul_right p.wordWidth slotNext
          _ = p.wordWidth * p.K := Nat.mul_comm _ _
          _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _⟩)) := by
  have physicalLt : slot.val * p.wordWidth + bit.val <
      (canonicalSortedOutputWires p kind).length := by
    rw [canonicalSortedOutputWires_length]
    simp only [QParameters.systemWidth]
    have slotNext : slot.val + 1 ≤ p.K := Nat.succ_le_of_lt slot.isLt
    calc
      slot.val * p.wordWidth + bit.val <
          slot.val * p.wordWidth + p.wordWidth :=
        Nat.add_lt_add_left bit.isLt _
      _ = (slot.val + 1) * p.wordWidth := by rw [Nat.succ_mul]
      _ ≤ p.K * p.wordWidth := Nat.mul_le_mul_right p.wordWidth slotNext
      _ = p.wordWidth * p.K := Nat.mul_comm _ _
      _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
  have found :
      (canonicalSortedOutputWires p kind)[slot.val * p.wordWidth + bit.val]? =
        some ((canonicalSortedOutputWires p kind).get
          ⟨slot.val * p.wordWidth + bit.val, physicalLt⟩) := by
    simp
  simp only [readWires, registerWordAt, List.getElem?_map,
    List.getElem?_take, bit.isLt, if_true, List.getElem?_drop]
  rw [found]
  rfl

/--
configuration候補を用いるsorted-data foldの各物理bit作用は、delimiterより前では
configuration bitのXOR、delimiter以後では恒等作用である。
-/
theorem writeSortedDataReference_configuration_wire_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (physical : Fin p.systemWidth) :
    let wire := canonicalSortedOutputWireAt p kind physical
    writeSortedDataReference p (canonicalSortedOutputWires p kind)
        configuration.1.card configuration.2.2 true input wire =
      if _before : physical.val < p.wordWidth * configuration.1.card then
        if delimiterEncoding configuration physical then !input wire
        else input wire
      else input wire := by
  dsimp only
  by_cases before : physical.val < p.wordWidth * configuration.1.card
  · rw [dif_pos before]
    let slot : Fin configuration.1.card :=
      ⟨physical.val / p.wordWidth,
        (Nat.div_lt_iff_lt_mul (by
          simp [QParameters.wordWidth, p.q_pos])).2
            (by simpa [Nat.mul_comm] using before)⟩
    let bit : Fin p.wordWidth :=
      ⟨physical.val % p.wordWidth,
        Nat.mod_lt _ (by simp [QParameters.wordWidth, p.q_pos])⟩
    let registerSlot : Fin p.K :=
      ⟨slot.val, lt_of_lt_of_le slot.isLt configuration.2.2⟩
    have physicalEq : physical =
        configurationWordIndex configuration slot bit := by
      apply Fin.ext
      simp only [configurationWordIndex]
      dsimp [slot, bit]
      exact (Nat.div_add_mod physical.val p.wordWidth).symm
    let outputState := writeSortedDataReference p
      (canonicalSortedOutputWires p kind) configuration.1.card
        configuration.2.2 true input
    have wordResult :=
      writeSortedDataReference_read_configuration_word_canonical p kind
        configuration input valuesEqual slot
    change readWires (registerWordAt p (canonicalSortedOutputWires p kind)
        registerSlot) outputState =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (siteWordBits p (configuration.siteAt slot))
        (readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          registerSlot) input) at wordResult
    have bitResult := congrArg (fun bits => bits[bit.val]?.getD false) wordResult
    have sourceGet :
        (siteWordBits p (configuration.siteAt slot))[bit.val]? =
          some (siteBit p (configuration.siteAt slot) bit) := by
      simp [siteWordBits, bit.isLt]
    have outputGet :
        (readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          ⟨slot.val, lt_of_lt_of_le slot.isLt configuration.2.2⟩)
            outputState)[bit.val]? =
          some (outputState ((canonicalSortedOutputWires p kind).get
            ⟨slot.val * p.wordWidth + bit.val, by
              rw [canonicalSortedOutputWires_length]
              simp only [QParameters.systemWidth]
              have slotNext : slot.val + 1 ≤ p.K :=
                Nat.succ_le_of_lt
                  (lt_of_lt_of_le slot.isLt configuration.2.2)
              calc
                slot.val * p.wordWidth + bit.val <
                    slot.val * p.wordWidth + p.wordWidth :=
                  Nat.add_lt_add_left bit.isLt _
                _ = (slot.val + 1) * p.wordWidth := by rw [Nat.succ_mul]
                _ ≤ p.K * p.wordWidth :=
                  Nat.mul_le_mul_right p.wordWidth slotNext
                _ = p.wordWidth * p.K := Nat.mul_comm _ _
                _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _⟩)) := by
      simpa [registerSlot] using
        readWires_canonicalRegisterWord_getElem p kind registerSlot bit outputState
    have inputGet :
        (readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          ⟨slot.val, lt_of_lt_of_le slot.isLt configuration.2.2⟩)
            input)[bit.val]? =
          some (input ((canonicalSortedOutputWires p kind).get
            ⟨slot.val * p.wordWidth + bit.val, by
              rw [canonicalSortedOutputWires_length]
              simp only [QParameters.systemWidth]
              have slotNext : slot.val + 1 ≤ p.K :=
                Nat.succ_le_of_lt
                  (lt_of_lt_of_le slot.isLt configuration.2.2)
              calc
                slot.val * p.wordWidth + bit.val <
                    slot.val * p.wordWidth + p.wordWidth :=
                  Nat.add_lt_add_left bit.isLt _
                _ = (slot.val + 1) * p.wordWidth := by rw [Nat.succ_mul]
                _ ≤ p.K * p.wordWidth :=
                  Nat.mul_le_mul_right p.wordWidth slotNext
                _ = p.wordWidth * p.K := Nat.mul_comm _ _
                _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _⟩)) := by
      simpa [registerSlot] using
        readWires_canonicalRegisterWord_getElem p kind registerSlot bit input
    rw [outputGet, List.getElem?_zipWith, sourceGet, inputGet] at bitResult
    simp only [Option.getD_some] at bitResult
    rw [physicalEq, delimiterEncoding_word]
    simpa [registerSlot, canonicalSortedOutputWireAt,
      configurationWordIndex, slot, bit, outputState, Nat.mul_comm]
      using bitResult
  · rw [dif_neg before]
    by_cases inWords : physical.val < p.wordWidth * p.K
    · let slot : Fin p.K :=
        ⟨physical.val / p.wordWidth,
          (Nat.div_lt_iff_lt_mul (by
            simp [QParameters.wordWidth, p.q_pos])).2
              (by
                calc
                  physical.val < p.wordWidth * p.K := inWords
                  _ = p.K * p.wordWidth := Nat.mul_comm _ _)⟩
      let bit : Fin p.wordWidth :=
        ⟨physical.val % p.wordWidth,
          Nat.mod_lt _ (by simp [QParameters.wordWidth, p.q_pos])⟩
      have padding : configuration.1.card ≤ slot.val := by
        dsimp [slot]
        by_contra notPadding
        have slotBefore : physical.val / p.wordWidth <
            configuration.1.card := Nat.lt_of_not_ge notPadding
        have wordWidthPositive : 0 < p.wordWidth := by
          exact Nat.mul_pos (by omega) p.q_pos
        have bitBound := Nat.mod_lt physical.val wordWidthPositive
        exact before <| calc
          physical.val = p.wordWidth * (physical.val / p.wordWidth) +
              physical.val % p.wordWidth :=
            (Nat.div_add_mod physical.val p.wordWidth).symm
          _ < p.wordWidth * (physical.val / p.wordWidth) + p.wordWidth :=
            Nat.add_lt_add_left bitBound _
          _ = p.wordWidth * (physical.val / p.wordWidth + 1) := by
            rw [Nat.mul_succ]
          _ ≤ p.wordWidth * configuration.1.card :=
            Nat.mul_le_mul_left p.wordWidth (Nat.succ_le_of_lt slotBefore)
      let outputState := writeSortedDataReference p
        (canonicalSortedOutputWires p kind) configuration.1.card
          configuration.2.2 true input
      have wordResult :=
        writeSortedDataReference_read_padding_word_canonical p kind
          configuration.1.card configuration.2.2 slot padding true input
      change readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          slot) outputState =
        readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          slot) input at wordResult
      have bitResult := congrArg (fun bits => bits[bit.val]?.getD false) wordResult
      have outputGet := readWires_canonicalRegisterWord_getElem p kind slot bit
        outputState
      have inputGet := readWires_canonicalRegisterWord_getElem p kind slot bit input
      rw [outputGet, inputGet] at bitResult
      simp only [Option.getD_some] at bitResult
      have physicalDecomposition :
          slot.val * p.wordWidth + bit.val = physical.val := by
        dsimp [slot, bit]
        calc
          physical.val / p.wordWidth * p.wordWidth +
              physical.val % p.wordWidth =
            p.wordWidth * (physical.val / p.wordWidth) +
              physical.val % p.wordWidth := by
                rw [Nat.mul_comm]
          _ = physical.val := Nat.div_add_mod physical.val p.wordWidth
      simpa [canonicalSortedOutputWireAt, physicalDecomposition, outputState]
        using bitResult
    · have physicalAtEnd : physical.val = p.wordWidth * p.K := by
        have physicalBound : physical.val < p.wordWidth * p.K + 1 := by
          simpa [QParameters.systemWidth] using physical.isLt
        omega
      have finalResult := writeSortedDataReference_finalWire_canonical p kind
        configuration.1.card configuration.2.2 true input
      simpa [canonicalSortedOutputWireAt, canonicalSortedOutputFinalWire,
        physicalAtEnd] using finalResult

/--
canonical candidateを用いるsorted-use全体は、configurationのdelimiter符号bitを
対応出力wireへ厳密にXORする。
-/
theorem writeSortedUseReference_configuration_wire_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (physical : Fin p.systemWidth) :
    let wire := canonicalSortedOutputWireAt p kind physical
    writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) configuration.1.card
        configuration.2.2 true input wire =
      if delimiterEncoding configuration physical then !input wire
      else input wire := by
  dsimp only
  let output := canonicalSortedOutputWires p kind
  let active := canonicalSortedOutputActive p kind
  let wire := canonicalSortedOutputWireAt p kind physical
  let copied := writeSortedDataReference p output configuration.1.card
    configuration.2.2 true input
  have delimiterLt : p.wordWidth * configuration.1.card < output.length := by
    rw [show output.length = p.systemWidth by
      exact canonicalSortedOutputWires_length p kind]
    simp only [QParameters.systemWidth]
    exact Nat.lt_succ_of_le
      (Nat.mul_le_mul_left p.wordWidth configuration.2.2)
  let delimiterWire := output.get
    ⟨p.wordWidth * configuration.1.card, delimiterLt⟩
  have wireMember : wire ∈ output := by
    unfold wire canonicalSortedOutputWireAt
    exact List.get_mem output ⟨physical.val, by
      rw [show output.length = p.systemWidth by
        exact canonicalSortedOutputWires_length p kind]
      exact physical.isLt⟩
  have wireDifferentActive : wire ≠ active := by
    intro equal
    apply canonicalSortedOutputActive_not_mem_output p kind
    rw [← show active = canonicalSortedOutputActive p kind by rfl]
    rw [← equal]
    exact wireMember
  have dataResult := writeSortedDataReference_configuration_wire_canonical
    p kind configuration input valuesEqual physical
  have useEq :
      writeSortedUseReference p output
          (canonicalSortedOutputWires_length p kind) active
          configuration.1.card configuration.2.2 true input wire =
        xBasisAction active (xBasisAction delimiterWire copied) wire := by
    unfold writeSortedUseReference
    simp only [if_true]
    rw [toggleOutputIndexReference_of_lt true output
      (p.wordWidth * configuration.1.card) delimiterLt copied]
    rfl
  rw [useEq, xBasisAction_other active wire wireDifferentActive]
  by_cases atDelimiter : physical.val = p.wordWidth * configuration.1.card
  · have wireEqDelimiter : wire = delimiterWire := by
      apply (List.Nodup.getElem_inj_iff
        (canonicalSortedOutputWires_nodup p kind)).2
      exact atDelimiter
    rw [wireEqDelimiter, xBasisAction_target]
    have notBefore : ¬physical.val <
        p.wordWidth * configuration.1.card := by omega
    have copiedValue : copied wire = input wire := by
      simpa [copied, output, wire, notBefore] using dataResult
    have delimiterValue : delimiterEncoding configuration physical = true := by
      have physicalEq : physical = delimiterIndex configuration := by
        apply Fin.ext
        exact atDelimiter
      rw [physicalEq]
      exact delimiterEncoding_delimiter configuration
    have copiedDelimiter : copied delimiterWire = input delimiterWire := by
      rw [← wireEqDelimiter]
      exact copiedValue
    rw [copiedDelimiter]
    have canonicalEqDelimiter :
        canonicalSortedOutputWireAt p kind physical = delimiterWire :=
      wireEqDelimiter
    rw [canonicalEqDelimiter, delimiterValue]
    simp
  · have wireDifferentDelimiter : wire ≠ delimiterWire := by
      intro equal
      apply atDelimiter
      apply (List.Nodup.getElem_inj_iff
        (canonicalSortedOutputWires_nodup p kind)).1
      simpa [wire, delimiterWire, output, canonicalSortedOutputWireAt]
        using equal
    rw [xBasisAction_other delimiterWire wire wireDifferentDelimiter]
    by_cases before : physical.val < p.wordWidth * configuration.1.card
    · simpa [copied, output, wire, before] using dataResult
    · have after : p.wordWidth * configuration.1.card < physical.val := by
        omega
      have delimiterValue : delimiterEncoding configuration physical = false :=
        delimiterEncoding_after_delimiter configuration physical after
      simpa [copied, output, wire, before, delimiterValue] using dataResult

/--
canonical sorted-useは、出力register全体ではdelimiter符号bit列のbitwise XORに一致する。
-/
theorem writeSortedUseReference_configuration_bits_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration) :
    readWires (canonicalSortedOutputWires p kind)
        (writeSortedUseReference p (canonicalSortedOutputWires p kind)
          (canonicalSortedOutputWires_length p kind)
          (canonicalSortedOutputActive p kind) configuration.1.card
          configuration.2.2 true input) =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (registerBitList (delimiterEncoding configuration))
        (readWires (canonicalSortedOutputWires p kind) input) := by
  apply List.ext_get
  · simp [readWires, registerBitList]
  · intro index leftInRange rightInRange
    let physical : Fin p.systemWidth := ⟨index, by
      simpa [readWires] using leftInRange⟩
    have pointResult := writeSortedUseReference_configuration_wire_canonical
      p kind configuration input valuesEqual physical
    simpa [readWires, registerBitList, canonicalSortedOutputWireAt, physical]
      using pointResult

/-- canonical sorted-useは、出力active signalを厳密に一回反転する。 -/
theorem writeSortedUseReference_configuration_active_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) configuration.1.card
        configuration.2.2 true input
        (canonicalSortedOutputActive p kind) =
      !input (canonicalSortedOutputActive p kind) := by
  let output := canonicalSortedOutputWires p kind
  let active := canonicalSortedOutputActive p kind
  let copied := writeSortedDataReference p output configuration.1.card
    configuration.2.2 true input
  have activeOutside : active ∉ output := by
    simpa [active, output] using canonicalSortedOutputActive_not_mem_output p kind
  have copiedActive : copied active = input active := by
    exact writeSortedDataReference_outside p output configuration.1.card
      configuration.2.2 true input active activeOutside
  have delimiterActive :
      toggleOutputIndexReference true output
          (p.wordWidth * configuration.1.card) copied active = copied active :=
    toggleOutputIndexReference_outside true output
      (p.wordWidth * configuration.1.card) copied active activeOutside
  unfold writeSortedUseReference
  simp only [if_true]
  rw [xBasisAction_target, delimiterActive, copiedActive]

end ReversibleCircuit

end ProbabilityGeneratorQProof
