import QLean.History.Implementation.HistoryPipelineQbPlusCleanBlock

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryCore

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryQbPlusCleanBlock

noncomputable section

/-! This module deliberately does not use `realPreparationCircuit023`: that
    definition is a choice over a witness whose only circuit theorem is its
    zero-input column.  The following witness is rebuilt by the binary
    construction, so its source-order equation remains visible in the proof. -/

structure CanonicalRealPreparation119 (n : Nat)
    (amplitude : QubitBasis n → ℝ) where
  circuit : NormalizedCircuit (prepWidth023 n)
  prepares :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) circuit.circuit)
        (basisKet (zeroBasis119 (prepWidth023 n))) =
      stateFromAmplitude023 n amplitude
  clean : CleanWorkTrace023 n (stateFromAmplitude023 n amplitude)

theorem existsCanonicalRealPreparationSucc119 :
    ∀ n (amplitude : QubitBasis (n + 1) → ℝ),
      realEnergy023 amplitude = 1 →
        Nonempty (CanonicalRealPreparation119 (n + 1) amplitude) := by
  intro n
  induction n with
  | zero =>
      intro amplitude normOne
      exact ⟨{
        circuit := baseNormalizedCircuit023 amplitude
        prepares := basePreparation023
        clean := baseCleanTrace023 amplitude }⟩
  | succ n ih =>
      intro amplitude normOne
      have leftNormOne :
          realEnergy023 (normalizedBranchAmplitude023 false amplitude) = 1 :=
        normalizedBranchAmplitude023_norm false amplitude
      have rightNormOne :
          realEnergy023 (normalizedBranchAmplitude023 true amplitude) = 1 :=
        normalizedBranchAmplitude023_norm true amplitude
      rcases ih (normalizedBranchAmplitude023 false amplitude) leftNormOne with
        ⟨leftWitness⟩
      rcases ih (normalizedBranchAmplitude023 true amplitude) rightNormOne with
        ⟨rightWitness⟩
      let angle : ℝ := 2 * Real.arccos (branchNorm119 false amplitude)
      have hcos : Real.cos (angle / 2) = branchNorm119 false amplitude := by
        dsimp [angle]
        rw [show (2 * Real.arccos (branchNorm119 false amplitude)) / 2 =
          Real.arccos (branchNorm119 false amplitude) by ring]
        exact branchAngle_cos023 normOne
      have hsin : Real.sin (angle / 2) = branchNorm119 true amplitude := by
        dsimp [angle]
        rw [show (2 * Real.arccos (branchNorm119 false amplitude)) / 2 =
          Real.arccos (branchNorm119 false amplitude) by ring]
        exact branchAngle_sin023 normOne
      generalize hw : prepWidth023 (n + 1 + 1) = physicalWidth at *
      have hwidth : physicalWidth = prepWidth023 (n + 1) + 3 := by
        rw [← hw, prepWidth023]
      cases hwidth
      let circuit : NormalizedCircuit (prepWidth023 (n + 1) + 3) :=
        { circuit := branchCompositionCircuit119 angle
            leftWitness.circuit rightWitness.circuit
          normalized := branchCompositionCircuit119_isNormalized023 angle
            leftWitness.circuit rightWitness.circuit }
      have hprep := branchCompositionCircuit119_prepares angle
        leftWitness.circuit rightWitness.circuit
        (stateFromAmplitude023 (n + 1)
          (normalizedBranchAmplitude023 false amplitude))
        (stateFromAmplitude023 (n + 1)
          (normalizedBranchAmplitude023 true amplitude))
        leftWitness.prepares rightWitness.prepares
      have hprepZero :
          applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (branchCompositionCircuit119 angle leftWitness.circuit
                  rightWitness.circuit))
              (basisKet (zeroBasis119 (prepWidth023 (n + 1) + 3))) =
            (Real.cos (angle / 2) : ℂ) •
                fixedOutsideStateEmbedding (lowerPlacement119
                  (prepWidth023 (n + 1)))
                  (fun wire => if wire.1 = topControl119
                    (prepWidth023 (n + 1)) then false else false)
                  (stateFromAmplitude023 (n + 1)
                    (normalizedBranchAmplitude023 false amplitude)) +
              (Real.sin (angle / 2) : ℂ) •
                fixedOutsideStateEmbedding (lowerPlacement119
                  (prepWidth023 (n + 1)))
                  (fun wire => if wire.1 = topControl119
                    (prepWidth023 (n + 1)) then true else false)
                  (stateFromAmplitude023 (n + 1)
                    (normalizedBranchAmplitude023 true amplitude)) := by
        rw [branchComposition_zeroInput023
          (n := prepWidth023 (n + 1))]
        exact hprep
      have hprepZeroNorm := hprepZero
      rw [hcos, hsin] at hprepZeroNorm
      have hfalseOutside :
          (fun wire : OutsideWire (lowerPlacement119
              (prepWidth023 (n + 1))) =>
            if wire.1 = topControl119 (prepWidth023 (n + 1))
            then false else false) =
            (fun _ => false) := by
        funext wire
        simp
      rw [hfalseOutside] at hprepZeroNorm
      refine ⟨{
        circuit := circuit
        prepares := ?_
        clean := ?_ }⟩
      · dsimp [circuit]
        convert hprepZeroNorm using 1
        · exact congrArg (fun q : Nat => State (QubitBasis q)) hw
        · rfl
        · simpa using stateFromAmplitude023_succ_heq n amplitude
      · exact CleanWorkTrace023.step
          (amplitude := amplitude)
          (stateFromAmplitude023_succ_heq n amplitude)
          leftWitness.clean rightWitness.clean

theorem existsCanonicalRealPreparation119 {n : Nat}
    (positive : 0 < n) (amplitude : QubitBasis n → ℝ)
    (normOne : realEnergy023 amplitude = 1) :
    Nonempty (CanonicalRealPreparation119 n amplitude) := by
  cases n with
  | zero => omega
  | succ k =>
      simpa using existsCanonicalRealPreparationSucc119 k amplitude normOne

/-! Data image and pointwise support predicates.  The pointwise form is
    intentionally stronger than a basis-span membership assertion and is the
    form used to recover the explicit matrix support sum later. -/

def dataBasisEmbedding119 (n : Nat) :
    QubitBasis n → QubitBasis (prepWidth023 n) :=
  fixedOutsideBasisEmbedding (dataPlacement023 n) dataOutsideZero023

def imageSupported119 {n : Nat}
    (state : State (QubitBasis (prepWidth023 n))) : Prop :=
  ∀ basis, (∀ input, dataBasisEmbedding119 n input ≠ basis) →
    state basis = 0

/-! The selector block is handled on the whole physical preparation carrier.
    No reducing-subspace or column-support hypothesis is used here: the
    conjugated complement is obtained from unitarity and the all-zero column.
    Logical zero padding is a separate entrywise statement below. -/

def zeroPaddedAmplitude119 {ι n : Type}
    (embedding : ι ↪ n) (b : ι → ℝ) (physical : n → ℝ) : n → ℝ := by
  classical
  exact fun index => if h : ∃ logical, embedding logical = index then
      b (Classical.choose h) else physical index

theorem zeroPaddedAmplitude119_on_embedding {ι n : Type}
    (embedding : ι ↪ n) (b : ι → ℝ) (physical : n → ℝ) :
    ∀ logical, zeroPaddedAmplitude119 embedding b physical (embedding logical) =
      b logical := by
  intro logical
  classical
  simp [zeroPaddedAmplitude119]

end
end ExecutableHistoryCore
