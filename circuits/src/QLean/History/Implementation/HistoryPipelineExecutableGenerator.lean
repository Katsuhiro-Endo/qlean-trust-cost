import QLean.History.Implementation.HistoryPipelineExecutableHistoryAngles

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open HistoryBlockEncoding
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic

noncomputable section

def zeroScientificAngle119 : ScientificAngleExpr :=
  .rational 0 1 (by decide)

/-- These three fields are proof-free transport metadata in GeneratorRawSchema.  The
actual generated P17/P44 circuit is definitionally built from `q` and `K`;
it does not consume these metadata values. -/
def generatorSelectorMetadata119 : List ScientificAngleExpr :=
  [zeroScientificAngle119, zeroScientificAngle119, zeroScientificAngle119]

def generatorCoefficientMetadata119 (source : CommonSource119) :
    List ScientificAngleExpr :=
  List.ofFn (fun index : Fin source.historyParameters.taylorOrder =>
    taylorCoefficientAngle119 index.val)

/-- A sound raw generator packet.  Its executable P17/P44 child is selected
by exactly the same `QParameters` that defines `commonModelQ119`. -/
def generatorRaw119 (source : CommonSource119) : GeneratorRawSchema.RawP17P44Data206 :=
  { q := source.qParameters.q
    K := source.qParameters.K
    targetQubits := source.qParameters.ancillaWidth +
      source.qParameters.systemWidth + 1
    control := source.qParameters.ancillaWidth +
      source.qParameters.systemWidth
    placement := List.range (source.qParameters.ancillaWidth +
      source.qParameters.systemWidth)
    controlWork := []
    selectorAngles := generatorSelectorMetadata119
    coefficientAngles := generatorCoefficientMetadata119 source
    idleCoefficientAngle := idleCoefficientAngle119 }

theorem zeroScientificAngle119_core :
    CanonicalHistoryAdapter.ScientificAngleCore zeroScientificAngle119 := by
  simp [zeroScientificAngle119, CanonicalHistoryAdapter.ScientificAngleCore]

theorem taylorCoefficientAngle119_core (j : Nat) :
    CanonicalHistoryAdapter.ScientificAngleCore (taylorCoefficientAngle119 j) := by
  simp [taylorCoefficientAngle119, scientificTwo119, scientificNegInv119,
    CanonicalHistoryAdapter.ScientificAngleCore]

theorem idleCoefficientAngle119_core :
    CanonicalHistoryAdapter.ScientificAngleCore idleCoefficientAngle119 := by
  simp [idleCoefficientAngle119, scientificTwo119,
    CanonicalHistoryAdapter.ScientificAngleCore]

theorem generatorRaw119_admissible (source : CommonSource119) :
    GeneratorRawSchema.HistoryP17P44Admissible206 (generatorRaw119 source) := by
  refine {
    q_positive := source.qParameters.q_pos
    K_positive := source.qParameters.K_pos
    target_layout := ?_
    control_layout := ?_
    placement_layout := ?_
    control_work_empty := rfl
    selector_length := rfl
    selector_core := ?_
    coefficient_core := ?_
    idle_core := idleCoefficientAngle119_core }
  · simp [generatorRaw119]
  · simp [generatorRaw119]
  · simp [generatorRaw119]
  · intro angle member
    have angle_eq : angle = zeroScientificAngle119 := by
      simpa [generatorRaw119, generatorSelectorMetadata119] using member
    rw [angle_eq]
    exact zeroScientificAngle119_core
  · intro angle member
    rw [generatorRaw119] at member
    simp only [generatorCoefficientMetadata119, List.mem_ofFn] at member
    obtain ⟨index, rfl⟩ := member
    exact taylorCoefficientAngle119_core index.val

def generatedBinding119 (source : CommonSource119) :
    GeneratorRawSchema.GeneratedP17P44Binding206 (generatorRaw119 source) :=
  GeneratorRawSchema.generatedP17P44Binding206
    (generatorRaw119 source) (generatorRaw119_admissible source)

end

end ExecutableHistoryExecutableHistory
