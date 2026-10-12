import QLean.Generator.Implementation.BitonicNetworkCorrectness
import QLean.Circuits.Foundation.BitonicPermutationCorrectnessAnalytic

/-!
# Shared bitonic multiplicity semantics façade

The established Q import path now re-exports the shared proof declarations.
-/

namespace ProbabilityGeneratorQProof

export VerifiedCircuitCore
  (finiteValueCount typedBitonicValueStep_eq_comp_swap_of_swap
   typedBitonicValueStep_eq_self_of_not_swap
   finiteValueCount_typedBitonicValueStep
   finiteValueCount_runTypedBitonicValues)

end ProbabilityGeneratorQProof
