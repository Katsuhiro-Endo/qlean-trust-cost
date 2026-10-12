import QLean.MathematicalSpecifications.CoalescingWalkModel
import Mathlib.Data.BitVec

/-!
# Mathematical delimiter encoding

This file contains the definitions that determine the meaning of CP01 on the
complete delimiter-word space.  Proofs of injectivity and decoding laws live
in `DelimiterEncodingProofs`; they are checked by Lean but are not part of the
human approval reading set.
-/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.Targets

open QLean.MathematicalSpecifications.CoalescingWalkModel

noncomputable section

/-- Number of bits in one two-coordinate lattice-site word. -/
def siteWordWidth (parameters : CoalescingWalkModel.Parameters) : Nat :=
  2 * parameters.q

/-- Width of the sorted site words, one delimiter bit, and zero padding. -/
def delimiterWidth (parameters : CoalescingWalkModel.Parameters) : Nat :=
  siteWordWidth parameters * parameters.K + 1

/-- The complete delimiter-sign register, including illegal bit strings. -/
abbrev DelimiterWord (parameters : CoalescingWalkModel.Parameters) :=
  Fin (delimiterWidth parameters) → Bool

/-- The lattice-site cardinality equals the capacity of one site word.  This
short proof term establishes the type cast used by `siteBitVector`. -/
theorem siteCapacity_eq (parameters : CoalescingWalkModel.Parameters) :
    parameters.G * parameters.G = 2 ^ siteWordWidth parameters := by
  simp [CoalescingWalkModel.Parameters.G, siteWordWidth, pow_add, two_mul]

/-- Little-endian word representing one mathematical lattice site. -/
def siteBitVector (parameters : CoalescingWalkModel.Parameters)
    (site : CoalescingWalkModel.Site parameters) :
    BitVec (siteWordWidth parameters) :=
  BitVec.ofFin (Fin.cast (siteCapacity_eq parameters) site)

/-- One bit of the independent little-endian site word. -/
def siteBit (parameters : CoalescingWalkModel.Parameters)
    (site : CoalescingWalkModel.Site parameters)
    (bit : Fin (siteWordWidth parameters)) : Bool :=
  (siteBitVector parameters site).getLsb bit

/-- Sorted occupied-site words, followed by one delimiter and zero padding.
This definition fixes the mathematical encoding but no physical wire layout. -/
def configurationEncoding (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters) :
    DelimiterWord parameters :=
  fun physicalBit =>
    if beforeDelimiter : physicalBit.val <
        siteWordWidth parameters * configuration.1.card then
      let slot : Fin configuration.1.card :=
        ⟨physicalBit.val / siteWordWidth parameters,
          (Nat.div_lt_iff_lt_mul (by
            simp [siteWordWidth, parameters.q_pos])).2
            (by simpa [Nat.mul_comm] using beforeDelimiter)⟩
      let wordBit : Fin (siteWordWidth parameters) :=
        ⟨physicalBit.val % siteWordWidth parameters,
          Nat.mod_lt _ (by
            simp [siteWordWidth, parameters.q_pos])⟩
      siteBit parameters (CoalescingWalkModel.siteAt configuration slot) wordBit
    else
      decide (physicalBit.val =
        siteWordWidth parameters * configuration.1.card)

/-- A word is legal precisely when it is the canonical encoding of one
approved mathematical configuration. -/
def IsLegalDelimiter (parameters : CoalescingWalkModel.Parameters)
    (bits : DelimiterWord parameters) : Prop :=
  ∃ configuration : CoalescingWalkModel.Configuration parameters,
    configurationEncoding parameters configuration = bits

/-- Decode a legal word and reject every other bit string.  On legal words the
chosen preimage is unique by the injectivity theorem in the proof-only file,
so the classical choice does not alter the mathematical target. -/
def decodeConfiguration (parameters : CoalescingWalkModel.Parameters)
    (bits : DelimiterWord parameters) :
    Option (CoalescingWalkModel.Configuration parameters) := by
  classical
  exact if legal : IsLegalDelimiter parameters bits then
    some (Classical.choose legal)
  else
    none

end

end QLean.MathematicalSpecifications.Targets
