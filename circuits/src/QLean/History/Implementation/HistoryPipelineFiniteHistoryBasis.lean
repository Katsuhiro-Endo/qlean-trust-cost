import QLean.History.Implementation.HistoryPipelineHistoryEmbedding
import QLean.Circuits.Foundation.ComputableRegisterWrite

/-!
Finite register encoding of the history basis.  The numerical constructor
accepts explicit finite register placements.  The theorem below identifies
its result with the legacy analytic basis at every old history index.  The
independent issue of how to compute the scientific layout and index order is
not hidden in this constructor.
-/

set_option autoImplicit false
set_option warningAsError true

namespace ExecutableHistoryHistoryEmbedding

open VerifiedCircuitCore
open ExecutableHistoryExecutableHistory

/-- Write data, clock and order into explicit registers using only finite
wire lookup.  This is executable for supplied register maps and bit words. -/
def finiteHistoryBasisAtRegisters {qubits dataWidth clockWidth orderWidth : Nat}
    (data : Register qubits dataWidth)
    (clock : Register qubits clockWidth)
    (order : Register qubits orderWidth)
    (dataBits : QubitBasis dataWidth)
    (clockBits : QubitBasis clockWidth)
    (orderBits : QubitBasis orderWidth) : QubitBasis qubits :=
  writeRegisterBitsFinite data dataBits
    (writeRegisterBitsFinite clock clockBits
      (writeRegisterBitsFinite order orderBits (fun _ => false)))

theorem finiteHistoryBasisAtRegisters_eq {qubits dataWidth clockWidth orderWidth : Nat}
    (data : Register qubits dataWidth)
    (clock : Register qubits clockWidth)
    (order : Register qubits orderWidth)
    (dataBits : QubitBasis dataWidth)
    (clockBits : QubitBasis clockWidth)
    (orderBits : QubitBasis orderWidth) :
    finiteHistoryBasisAtRegisters data clock order dataBits clockBits orderBits =
      writeRegisterBits data dataBits
        (writeRegisterBits clock clockBits
          (writeRegisterBits order orderBits (fun _ => false))) := by
  simp only [finiteHistoryBasisAtRegisters, writeRegisterBitsFinite_eq]

/-- Pointwise link to the existing scientific history basis.  This does not
assert that the scientific raw layout or its legacy numbering is computable. -/
theorem finiteHistoryBasisAtRegisters_scientific_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    finiteHistoryBasisAtRegisters
        (ExecutableLayout119 source domain).data
        (ExecutableLayout119 source domain).clock
        (ExecutableLayout119 source domain).order
        (dataBits119 source index.state.configuration)
        (clockBits119 source fits index)
        (orderBits119 source fits index) =
      executableHistoryBasis119 source domain fits index := by
  exact finiteHistoryBasisAtRegisters_eq _ _ _ _ _ _

end ExecutableHistoryHistoryEmbedding
