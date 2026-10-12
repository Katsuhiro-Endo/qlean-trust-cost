import Mathlib

namespace HistoryBlockEncoding
namespace ModelQ

noncomputable section

/-- Number of active events taking an input configuration to an output one. -/
def transitionCount
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) : Nat :=
  ((events input).filter fun event => update input event = output).card

/-- Column-convention probability generator from configuration/event/update data. -/
def probabilityGenerator
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) : ℚ :=
  if output = input then
    -(particleCount input : ℚ)
  else
    (transitionCount events update output input : ℚ) / 2

/-- The model matrix; its indices are configurations, not physical wires. -/
def modelMatrix
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration) :
    Matrix Configuration Configuration ℚ :=
  fun output input => probabilityGenerator particleCount events update output input

@[simp] theorem modelMatrix_apply
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) :
    modelMatrix particleCount events update output input =
      probabilityGenerator particleCount events update output input := rfl

/-- A pure encoding boundary with explicit zero completion outside the image. -/
structure Encoding (Configuration Basis : Type*) where
  encode : Configuration → Basis
  decode : Basis → Option Configuration
  decode_encode : ∀ configuration, decode (encode configuration) = some configuration

/-- Zero-completed matrix on the physical basis induced by a pure encoding. -/
def encodedMatrix
    {Configuration Basis : Type*}
    (decode : Basis → Option Configuration)
    (matrix : Matrix Configuration Configuration ℚ) :
    Matrix Basis Basis ℚ :=
  fun output input =>
    match decode output, decode input with
    | some outputConfiguration, some inputConfiguration => matrix outputConfiguration inputConfiguration
    | _, _ => 0

theorem encodedMatrix_encode
    {Configuration Basis : Type*}
    (encoding : Encoding Configuration Basis)
    (matrix : Matrix Configuration Configuration ℚ)
    (output input : Configuration) :
    encodedMatrix encoding.decode matrix (encoding.encode output) (encoding.encode input) =
      matrix output input := by
  simp [encodedMatrix, encoding.decode_encode]

end

end ModelQ
end HistoryBlockEncoding
