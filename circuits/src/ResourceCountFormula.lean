import QLean.Circuits.FiniteKernelResources

open VerifiedCircuitCore M13bFiniteOuterCompiler

namespace ResourceCountFormula

def weightedCount {G : Type} (weight : G → Nat) : Circuit G → Nat
  | .identity => 0
  | .gate g => weight g
  | .seq a b => weightedCount weight a + weightedCount weight b
  | .repeat n a => n * weightedCount weight a

theorem weightedCount_eq {G : Type} (weight : G → Nat) (c : Circuit G) :
    weightedCount weight c = (c.flatten.map weight).sum := by
  induction c with
  | identity => rfl
  | gate g => simp [weightedCount, Circuit.flatten]
  | seq a b ha hb => simp [weightedCount, Circuit.flatten, ha, hb]
  | «repeat» n a ha =>
    induction n with
    | zero => simp [weightedCount, Circuit.flatten]
    | succ n ih =>
      simp only [weightedCount, Circuit.flatten, List.replicate_succ,
        List.flatten_cons, List.map_append, List.sum_append] at ih ⊢
      rw [Nat.succ_mul, ih, ha, Nat.add_comm]

def fastControlCost {n m : Nat} (layout : ExternallyControlledCircuitLayout n m)
    (c : Circuit (PrimitiveGate n)) : Nat := weightedCount (leafCost layout) c

theorem fastControlCost_eq {n m : Nat} (layout : ExternallyControlledCircuitLayout n m)
    (c : Circuit (PrimitiveGate n)) : fastControlCost layout c = controlCost layout c :=
  weightedCount_eq _ _

def fastPlannedCount (input : QLean.Circuits.FiniteKernelCircuit.Input) : Nat :=
  let plan := input.source.outerPlan input.fits
  let s := fastControlCost plan.layout plan.signalCircuit
  let p := fastControlCost plan.layout (input.source.imagePhaseCircuit input.fits .pi)
  let request := input.polynomialRequest
  11 + 4 * (request.degree*s + request.phaseCount*p) + p

theorem fastPlannedCount_correct (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    fastPlannedCount input =
      (QLean.Circuits.FiniteKernelCircuit.kernelReflectionCircuit input
        VerifiedMath.Quantum.QSP.defaultPhaseProvider).gateCount := by
  rw [← QLean.Circuits.FiniteKernelCircuit.plannedGateCount_default]
  simp only [fastPlannedCount, fastControlCost_eq,
    QLean.Circuits.FiniteKernelCircuit.plannedGateCount,
    QLean.Circuits.FiniteKernelCircuit.signalGateCount,
    QLean.Circuits.FiniteKernelCircuit.phaseGateCount]


@[noinline] def embeddingBox {n m : Nat} (p : Fin n ↪ Fin m) (outside : QubitBasis m) :
    (QubitBasis n → QubitBasis m) × Nat :=
  let lookup := Array.ofFn (finitePlacementLookup p)
  (fun bits wire => match lookup[wire.val]'(by simp [lookup]) with
    | some i => bits i
    | none => outside wire, 0)

def cachedEmbedding {n m : Nat} (p : Fin n ↪ Fin m) (outside : QubitBasis m) :
    QubitBasis n → QubitBasis m := (embeddingBox p outside).1

theorem cachedEmbedding_eq {n m : Nat} (p : Fin n ↪ Fin m) (outside : QubitBasis m) :
    (embeddingBox p outside).1 = fun bits => finiteFixedOutsideBasisEmbedding p outside bits := by
  funext bits wire
  simp only [embeddingBox, Array.getElem_ofFn]
  rfl

open QLean.Circuits.FiniteScientificCircuitSource
open ExecutableHistoryImplementationRole ExecutableHistoryCore
open ExecutableHistoryHistoryEmbedding ExecutableHistoryFiniteScientificH3
open ExecutableHistoryQbPlusCleanBlock ExecutableHistoryAlignedPhysicalP18
open ScientificExtractionPhysicalSpecification
open ExecutableHistoryExecutableP18 ExecutableHistoryExecutableHistory

@[noinline] def historyBox (input : QLean.Circuits.FiniteKernelCircuit.Input) :=
  let source := input.source.layoutSource
  let configurations := Array.ofFn (ProbabilityGeneratorQProof.configurationEquivCard source.qParameters).symm
  (fun (index : JenningsHistory.HistoryIndex
      (Fintype.card (ProbabilityGeneratorQProof.QConfiguration source.qParameters))
      source.historyParameters.clockEnd source.historyParameters.binaryLabels) =>
    let oldIndex : OldHistoryIndex119 source :=
      { clock := index.clock
        state := { label := index.order
                   configuration := configurations[index.state.val]'(by simp [configurations]) } }
    finiteHistoryBasisAtRegisters
      (finiteScientificHistoryDataRegister119 source)
      (finiteScientificHistoryClockRegister119 source)
      (finiteScientificHistoryOrderRegister119 source)
      (fun bit => ProbabilityGeneratorQProof.delimiterEncoding oldIndex.state.configuration bit)
      (clockBits119 source input.fits oldIndex)
      (orderBits119 source input.fits oldIndex), (0 : Nat))

def cachedHistoryBasis (input : QLean.Circuits.FiniteKernelCircuit.Input) := (historyBox input).1

theorem cachedHistoryBasis_eq (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    (historyBox input).1 = finiteScientificCanonicalHistoryBasis119 input.source.layoutSource input.fits := by
  funext index
  simp only [historyBox, Array.getElem_ofFn,
    finiteScientificCanonicalHistoryBasis119, canonicalOldHistoryIndex119]

@[noinline] def sourceBox (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    (GramOperator.ExtendedIndex
      (Fintype.card (ProbabilityGeneratorQProof.QConfiguration input.source.qParameters))
      input.source.historyParameters.clockEnd input.source.historyParameters.binaryLabels →
      QubitBasis input.source.p18Qubits) × Nat :=
  let source := input.source
  let plan := finiteScientificHistorySourcePlan119 source.layoutSource input.fits source.branchLayout
  let yes := (embeddingBox plan.layout.placement (finiteBranchOutside119 plan.layout true)).1
  let no := (embeddingBox plan.layout.placement (finiteBranchOutside119 plan.layout false)).1
  let align := (embeddingBox (dataPlacement023 source.branchQubits) (fun _ => false)).1
  let block := (embeddingBox (dataPlacement119 source.preparationQubits) (fun _ => false)).1
  let history := (historyBox input).1
  (fun index wire =>
    let branch := match index with
      | Sum.inl row => yes (history row)
      | Sum.inr _ => no plan.inrBasis
    if wire = signalWire119 source.preparationQubits then false else block (align branch) wire, 0)

def cachedSourceBasis (input : QLean.Circuits.FiniteKernelCircuit.Input) := (sourceBox input).1

theorem cachedSourceBasis_eq (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    (sourceBox input).1 = input.source.sourceBasis input.fits := by
  funext index wire
  change (sourceBox input).1 index wire = _
  simp only [sourceBox,
    cachedHistoryBasis_eq, cachedEmbedding_eq,
    FiniteScientificSource.sourceBasis, NativeSignalQSVTActual.finiteSignalBasis119,
    finiteBlockBasis119, finiteExtendedIndexBasisOfPlan119, finiteBranchBasisEmbedding119]
  cases index <;> simp <;> rfl

def cachedPhaseCost (input : QLean.Circuits.FiniteKernelCircuit.Input) : Nat :=
  let source := input.source
  let rows := ScientificExtractionPhysicalSpecification.finiteExtendedHistoryRows119
    (Fintype.card (ProbabilityGeneratorQProof.QConfiguration source.qParameters))
    source.historyParameters.clockEnd source.historyParameters.binaryLabels
  let program := OrderedImagePhase.program rows (sourceBox input).1
  fastControlCost (source.outerPlan input.fits).layout
    (NativeExactBasisPhase.booleanProgramPhaseCircuitExpr program source.phaseScratch source.phaseFlag .pi)

theorem cachedPhaseCost_eq (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    cachedPhaseCost input = QLean.Circuits.FiniteKernelCircuit.phaseGateCount input := by
  simp only [cachedPhaseCost, cachedSourceBasis_eq, fastControlCost_eq,
    QLean.Circuits.FiniteKernelCircuit.phaseGateCount,
    FiniteScientificSource.imagePhaseCircuit, FiniteScientificSource.imagePhaseProgram]


def totalCount (input : QLean.Circuits.FiniteKernelCircuit.Input) : Nat :=
  let s := fastControlCost (input.source.outerPlan input.fits).layout
    (input.source.outerPlan input.fits).signalCircuit
  let p := cachedPhaseCost input
  11 + 4 * (input.polynomialRequest.degree*s + input.polynomialRequest.phaseCount*p) + p

theorem totalCount_correct (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    totalCount input =
      (QLean.Circuits.FiniteKernelCircuit.kernelReflectionCircuit input
        VerifiedMath.Quantum.QSP.defaultPhaseProvider).gateCount := by
  rw [← QLean.Circuits.FiniteKernelCircuit.plannedGateCount_default]
  simp only [totalCount, cachedPhaseCost_eq, fastControlCost_eq,
    QLean.Circuits.FiniteKernelCircuit.plannedGateCount,
    QLean.Circuits.FiniteKernelCircuit.signalGateCount]


theorem totalCount_cp04_correct (input : QLean.Circuits.FiniteKernelCircuit.Input) :
    totalCount input =
      (QLean.Circuits.FiniteKernelCircuit.successfulHistoryCircuit input
        VerifiedMath.Quantum.QSP.defaultPhaseProvider).gateCount :=
  totalCount_correct input

end ResourceCountFormula
