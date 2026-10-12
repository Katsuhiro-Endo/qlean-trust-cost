import QLean.History.Implementation.HistoryPipelineReferenceM10Bridge
import QLean.History.Implementation.HistoryPipelineReferenceRawValueConstructorV2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open HistoryBlockEncoding
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic

noncomputable section

/-! A sound common source: the mathematical generator is the matrix carried
by the same `QParameters` that is compiled by P44.  No model entry is packed
into the Taylor-angle stream. -/
structure CommonSource119 where
  qParameters : QParameters
  historyParameters : HistorySpec.Parameters
  historyWellFormed : HistorySpec.WellFormed historyParameters
  initial : QConfiguration qParameters → ℚ
  historyBlocks : Nat
  historyBlocksPositive : 0 < historyBlocks
  binaryLabelsExact :
    historyParameters.binaryLabels =
      historyIdleBlockSize historyParameters.taylorOrder
  clockEndExact :
    historyParameters.clockEnd =
      historyParameters.physicalClocks + historyBlocks
  stepPositive : 0 < historyParameters.stepSize
  scaledStepSmall :
    (3 * (qParameters.K : ℝ)) * (historyParameters.stepSize : ℝ) ≤ 1
  targetStateError : ℝ
  targetStateErrorPositive : 0 < targetStateError

def commonModelQ119 (source : CommonSource119) :
    Matrix (QConfiguration source.qParameters)
      (QConfiguration source.qParameters) ℚ :=
  HistoryBlockEncoding.QModel.configurationQMatrix

def generatorAlpha119 (p : QParameters) : ℝ := 3 * (p.K : ℝ)

def omegaH119 (source : CommonSource119) : ℝ :=
  generatorAlpha119 source.qParameters *
    (source.historyParameters.stepSize : ℝ)

theorem omegaH119_positive (source : CommonSource119) :
    0 < omegaH119 source := by
  have hK : 0 < (source.qParameters.K : ℝ) := by exact_mod_cast source.qParameters.K_pos
  have hh : 0 < (source.historyParameters.stepSize : ℝ) := by
    exact_mod_cast source.stepPositive
  unfold omegaH119 generatorAlpha119
  positivity

def scientificTwo119 : ScientificAngleExpr :=
  .rational 2 1 (by decide)

def scientificNegInv119 (j : Nat) : ScientificAngleExpr :=
  .rational (-1) (j + 1) (by omega)

/-- The physical Taylor coefficient used by the source emitter after the
order raise: its clean-signal amplitude is exactly `-1/(j+1)`. -/
def taylorCoefficientAngle119 (j : Nat) : ScientificAngleExpr :=
  .mul scientificTwo119 (.acos (scientificNegInv119 j))

/-- Idling uses the full binary order range and clean-signal amplitude `-1`. -/
def idleCoefficientAngle119 : ScientificAngleExpr :=
  .mul scientificTwo119 .pi

def compiledTaylorCoefficientAngle119 (j : Nat) :
    VerifiedCircuitCore.AngleExpr :=
  CanonicalHistoryAdapter.compileScientificAngle (taylorCoefficientAngle119 j)

def compiledIdleCoefficientAngle119 : VerifiedCircuitCore.AngleExpr :=
  CanonicalHistoryAdapter.compileScientificAngle idleCoefficientAngle119

def cleanSignalAmplitude119 (angle : VerifiedCircuitCore.AngleExpr) : ℝ :=
  Real.cos (angle.uniformValue / 2)

theorem compiledTaylorCoefficientAngle119_value (j : Nat) :
    (compiledTaylorCoefficientAngle119 j).uniformValue =
      2 * Real.arccos (-(1 : ℝ) / ((j + 1 : Nat) : ℝ)) := by
  simp [compiledTaylorCoefficientAngle119, taylorCoefficientAngle119,
    scientificTwo119, scientificNegInv119, CanonicalHistoryAdapter.compileScientificAngle,
    VerifiedCircuitCore.AngleExpr.uniformValue, VerifiedCircuitCore.AngleExpr.eval]

theorem compiledIdleCoefficientAngle119_value :
    compiledIdleCoefficientAngle119.uniformValue = 2 * Real.pi := by
  simp [compiledIdleCoefficientAngle119, idleCoefficientAngle119,
    scientificTwo119, CanonicalHistoryAdapter.compileScientificAngle,
    VerifiedCircuitCore.AngleExpr.uniformValue, VerifiedCircuitCore.AngleExpr.eval]

theorem idleCoefficient_clean_amplitude119 :
    cleanSignalAmplitude119 compiledIdleCoefficientAngle119 = -1 := by
  unfold cleanSignalAmplitude119
  rw [compiledIdleCoefficientAngle119_value]
  simp

end

end ExecutableHistoryExecutableHistory
