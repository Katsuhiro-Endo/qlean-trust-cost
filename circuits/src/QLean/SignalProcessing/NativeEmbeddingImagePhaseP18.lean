import QLean.SignalProcessing.RootPlacedEmbeddingImagePhase
import QLean.SignalProcessing.NativeSignalQSVTActual

/-!
# Two-frame exact image phases for the actual P18 signal circuit

The source and target frames are the distinct signal-bit embeddings
`(0, index)` and `(1, index)`.  The actual P18 signal circuit is separately
wire-lifted to the widened register; its two projector phases use typed clean
outside wires and preserve every phase angle as `AngleExpr.const angle`.
-/

namespace NativeSignalQSVTActual

open VerifiedCircuitCore
open VerifiedCircuitCore.NativeEmbeddingImagePhase
open ExecutableHistoryExecutableP18
open ExecutableHistoryExecutableHistory
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryQbPlusCleanBlock
open ExecutableHistoryAlignedPhysicalP18

noncomputable section

/-- Physical width of the actual P18 signal circuit. -/
abbrev ExecutableSignalP18Qubits119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions) : Nat :=
  blockQubits119 (AlignedDataQubits119
    (executableInternalHHistory119 source domain fits assumptions circuitSource))

/-- The actual P18 clean basis embedding for either signal frame.  Frames zero
and one are intentionally different physical computational-basis images. -/
def executableSignalFrameEmbedding119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (frame : Fin 2) :
    GramOperator.ExtendedIndex (ExecutableD119 source) (ExecutableC119 source)
        (ExecutableLabels119 source) ↪
      QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions
        circuitSource) where
  toFun := fun index => executableSignalEmbedding source domain fits assumptions
    circuitSource (frame, index)
  inj' := by
    intro left right equal
    have pairEqual :=
      (executableSignalEmbedding source domain fits assumptions circuitSource).injective
        equal
    exact congrArg Prod.snd pairEqual

/-- The distinct signal-zero (source) image. -/
def executableSignalSourceEmbedding119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions) :=
  executableSignalFrameEmbedding119 source domain fits assumptions circuitSource 0

/-- The actual P18 primitive signal circuit. -/
def executableSignalP18Circuit119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions) :
    Circuit (PrimitiveGate (ExecutableSignalP18Qubits119 source domain fits assumptions
      circuitSource)) :=
  (executableAlignedP18Program source domain fits assumptions circuitSource).signalCircuit

/-- Wire-lift the actual P18 signal circuit while retaining the extra outside
ancilla block for exact source/target phases. -/
def executableSignalP18WireLiftCircuit119
    {targetQubits : Nat}
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (placement : Fin (ExecutableSignalP18Qubits119 source domain fits assumptions
      circuitSource) ↪ Fin targetQubits) : Circuit (PrimitiveGate targetQubits) :=
  (executableSignalP18Circuit119 source domain fits assumptions circuitSource).mapGates
    (PrimitiveGate.mapWires placement)

end

end NativeSignalQSVTActual
